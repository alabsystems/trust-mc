#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Regression tests for tools/tuple-check (scripts/tuple_check.py).

Each failure test changes exactly one input of a hermetic fixture and pins the
exact set of checks that refuse it, so a check that stops firing, or starts
firing on an unrelated input, fails here.
"""

from __future__ import annotations

import json
import io
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import tuple_check
from test_development_seal import HOST as DEVELOPMENT_HOST, SealFixture


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts" / "tuple_check.py"
WRAPPER = ROOT / "tools" / "tuple-check"

TRUST_REV = "a" * 40
OTHER_REV = "b" * 40
TRUST_VC_REV = "c" * 40
CLEAN_REV = "d" * 40
KANI_SPEC_REV = "f" * 40
AY_PACKAGES = (
    "ay",
    "ay-bindings",
    "ay-chc",
    "ay-core",
    "ay-dpll",
    "ay-encode",
    "ay-frontend",
    "ay-sys",
)
GIT = (
    "git",
    "-c", "user.name=tuple-check fixture",
    "-c", "user.email=fixture@example.invalid",
    "-c", "commit.gpgsign=false",
    "-c", "core.hooksPath=/dev/null",
    "-c", "init.defaultBranch=main",
)


def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        [*GIT, "-C", str(repo), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def write(path: Path, text: str, *, executable: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    if executable:
        path.chmod(0o755)


def commit_all(repo: Path) -> str:
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", "fixture")
    return git(repo, "rev-parse", "HEAD")


def ay_manifest(rev: str, *, odd_one_out: str | None = None) -> str:
    lines = ["[workspace]", "[workspace.dependencies]"]
    for package in AY_PACKAGES:
        package_rev = odd_one_out if (odd_one_out and package == "ay-sys") else rev
        lines.append(
            f'{package.replace("-", "_")} = {{ package = "{package}", '
            f'git = "https://github.com/alabsystems/ay.git", rev = "{package_rev}" }}'
        )
    return "\n".join(lines) + "\n"


def member_manifest(trust_ir_rev: str, trust_vc_rev: str) -> str:
    return (
        '[package]\nname = "member"\nversion = "0.1.0"\n[dependencies]\n'
        f'trust_ir = {{ package = "trust-ir", git = "https://github.com/alabsystems/trust-ir.git", rev = "{trust_ir_rev}" }}\n'
        f'trust_ir-build = {{ package = "trust-ir-build", git = "https://github.com/alabsystems/trust-ir.git", rev = "{trust_ir_rev}" }}\n'
        f'trust-vc-merge-contract = {{ git = "https://github.com/alabsystems/trust-vc.git", rev = "{trust_vc_rev}" }}\n'
    )


def clean_manifest(rev: str) -> str:
    lines = ['[package]', 'name = "trust-ir"', 'version = "0.14.0"', "[dependencies]"]
    for package in ("clean-kernel", "clean-mathverse", "clean-olean"):
        lines.append(
            f'{package} = {{ git = "https://github.com/alabsystems/clean.git", rev = "{rev}" }}'
        )
    return "\n".join(lines) + "\n"


def lockfile(clean_rev: str, trust_vc_rev: str) -> str:
    return (
        "version = 4\n\n"
        '[[package]]\nname = "clean-kernel"\nversion = "0.9.0"\n'
        f'source = "git+https://github.com/alabsystems/clean.git?rev={clean_rev}#{clean_rev}"\n\n'
        '[[package]]\nname = "trust-ir"\nversion = "0.14.0"\n\n'
        '[[package]]\nname = "trust-vc-merge-contract"\nversion = "0.6.0"\n'
        f'source = "git+https://github.com/alabsystems/trust-vc.git?rev={trust_vc_rev}#{trust_vc_rev}"\n'
    )


def clone_rs(rev: str) -> str:
    return (
        "use std::path::Path;\n\n"
        "/// The default pinned Kani revision the corpus is measured against.\n"
        f'pub const DEFAULT_KANI_REV: &str = "{rev}";\n'
    )


def kani_spec_pins(corpus_rev: str, spec_rev: str) -> str:
    return (
        'schema = "trust-mc.kani-spec.pins/v1"\n'
        'upstream = "https://github.com/model-checking/kani"\n'
        f'[revs.corpus]\nrev = "{corpus_rev}"\nnightly = "nightly-2025-12-03"\n'
        f'[revs.spec]\nrev = "{spec_rev}"\nnightly = "nightly-2026-08-21"\n'
    )


def spec_manifest(kani_rev: str) -> str:
    return json.dumps(
        {"schema": "trust-mc.kani-spec.manifest/v1", "kani_rev": kani_rev}, indent=2
    ) + "\n"


def render_tuple(document: dict) -> str:
    lines = [f"schema = {document['schema']}"]
    for table, values in document.items():
        if table == "schema":
            continue
        lines.append(f"\n[{table}]")
        lines.extend(f"{key} = {json.dumps(value)}" for key, value in values.items())
    return "\n".join(lines) + "\n"


class Fixture:
    """A trust-mc root with ../ay and ../trust-ir siblings, a Kani corpus checkout
    and a fake seal."""

    def __init__(self, base: Path) -> None:
        self.base = base
        self.root = base / "trust-mc"
        self.ay = base / "ay"
        self.trust_ir = base / "trust-ir"

        write(self.ay / "README", "ay fixture\n")
        git(self.ay, "init", "-q")
        self.ay_rev = commit_all(self.ay)

        write(self.trust_ir / "Cargo.toml", clean_manifest(CLEAN_REV))
        git(self.trust_ir, "init", "-q")
        self.trust_ir_rev = commit_all(self.trust_ir)

        # Named to the checker through KANI_DOMINATION_CORPUS_DIR (see setUp),
        # outside the trust-mc root like the runner's real user-cache corpus.
        self.kani = self.base / "cache" / "kani-corpus"
        write(self.kani / "tests" / "kani" / "harness.rs", "fn main() {}\n")
        git(self.kani, "init", "-q")
        self.kani_rev = commit_all(self.kani)

        write(self.root / "Cargo.toml", ay_manifest(self.ay_rev))
        write(
            self.root / "member" / "Cargo.toml",
            member_manifest(self.trust_ir_rev, TRUST_VC_REV),
        )
        write(self.root / "Cargo.lock", lockfile(CLEAN_REV, TRUST_VC_REV))
        write(self.root / "rust-toolchain.toml", '[toolchain]\nchannel = "trust"\n')
        write(
            self.root / "rust-toolchain.legacy.toml",
            '[toolchain]\nchannel = "nightly-2025-12-03"\n',
        )
        write(
            self.root / "tools" / "kani-domination" / "src" / "clone.rs",
            clone_rs(self.kani_rev),
        )
        write(self.pins_path, kani_spec_pins(self.kani_rev, KANI_SPEC_REV))
        write(self.spec_manifest_path(self.kani_rev), spec_manifest(self.kani_rev))
        write(self.spec_manifest_path(KANI_SPEC_REV), spec_manifest(KANI_SPEC_REV))

        self.set_rustc_commit(TRUST_REV)
        self.set_sysroot(base / "store" / "trust" / "8560")
        write(
            base / "bin" / "trustc",
            f"#!/bin/sh\ncat '{base / 'rustc-vv.txt'}'\n",
            executable=True,
        )
        self.set_resolver_ok()

        self.tuple = {
            "schema": 1,
            "trust": {"rev": TRUST_REV, "build": 8560, "channel": "trust"},
            "frozen_toolchain": {"channel": "nightly-2025-12-03"},
            "ay": {"rev": self.ay_rev},
            "trust_ir": {"rev": self.trust_ir_rev},
            "trust_vc": {"rev": TRUST_VC_REV},
            "clean": {"rev": CLEAN_REV},
            "kani": {"corpus_rev": self.kani_rev, "spec_rev": KANI_SPEC_REV},
        }
        self.write_tuple()

    @property
    def pins_path(self) -> Path:
        return self.root / "tools" / "kani-spec" / "pins.toml"

    def spec_manifest_path(self, rev: str) -> Path:
        return self.root / "spec" / "kani" / rev / "manifest.json"

    @property
    def tuple_path(self) -> Path:
        return self.root / "tools" / "tuple.toml"

    def write_tuple(self) -> None:
        write(self.tuple_path, render_tuple(self.tuple))

    def set_rustc_commit(self, commit: str) -> None:
        write(
            self.base / "rustc-vv.txt",
            f"rustc 1.99.0-dev ({commit[:9]} 2026-09-10)\nbinary: rustc\n"
            f"commit-hash: {commit}\ncommit-date: 2026-09-10\n"
            "host: aarch64-apple-darwin\nrelease: 1.99.0-dev\ntrust: 0.1.0\n",
        )

    def set_sysroot(self, sysroot: Path) -> None:
        sysroot.mkdir(parents=True, exist_ok=True)
        write(self.base / "sysroot.txt", f"{sysroot}\n")

    def set_resolver_ok(self) -> None:
        write(
            self.root / "scripts" / "resolve-trust-tool.sh",
            "#!/bin/sh\n"
            'case "$1" in\n'
            f"  trustc) printf '%s\\n' '{self.base / 'bin' / 'trustc'}' ;;\n"
            f"  sysroot) cat '{self.base / 'sysroot.txt'}' ;;\n"
            "  *) exit 2 ;;\n"
            "esac\n",
            executable=True,
        )

    def report(self) -> dict:
        return tuple_check.evaluate(self.root, self.tuple_path)

    def check(self, report: dict, check_id: str) -> dict:
        return next(check for check in report["checks"] if check["id"] == check_id)


class TupleCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.fx = Fixture(Path(self._temporary.name).resolve())
        environment = mock.patch.dict(
            os.environ, {tuple_check.KANI_CORPUS_DIR_ENV: str(self.fx.kani)}
        )
        environment.start()
        self.addCleanup(environment.stop)
        # An override exported by whoever runs the tests must not leak in.
        os.environ.pop(tuple_check.TRUST_TOOLCHAIN_OVERRIDE_ENV, None)

    def _without_corpus_override(self, **variables: str) -> mock._patch_dict:
        """Patch the environment so the checker falls back to the user cache."""
        patch = mock.patch.dict(os.environ, variables)
        patch.start()
        self.addCleanup(patch.stop)
        for name in (tuple_check.KANI_CORPUS_DIR_ENV, "XDG_CACHE_HOME"):
            os.environ.pop(name, None)
        return patch

    def assertRefusedBy(self, expected: set[str], *fragments: str) -> dict:
        report = self.fx.report()
        self.assertFalse(report["ok"])
        self.assertEqual(set(report["failed"]), expected, report["checks"])
        messages = " | ".join(
            check["message"] for check in report["checks"] if check["status"] == "fail"
        )
        for fragment in fragments:
            self.assertIn(fragment, messages)
        return report

    # --- pass -------------------------------------------------------------

    def test_matching_tuple_passes_every_check_in_order(self) -> None:
        report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])
        self.assertEqual(report["failed"], [])
        self.assertEqual(report["unchecked"], [])
        self.assertEqual(
            tuple(check["id"] for check in report["checks"]), tuple_check.CHECK_IDS
        )
        self.assertEqual(self.fx.check(report, "trust.build")["actual"], "8560")
        self.assertEqual(self.fx.check(report, "ay.checkout")["actual"], self.fx.ay_rev)
        self.assertEqual(
            self.fx.check(report, "kani.checkout")["actual"], self.fx.kani_rev
        )
        spec = self.fx.check(report, "kani.spec")
        self.assertEqual(
            (spec["status"], spec["expected"], spec["actual"], spec["source"]),
            ("pass", KANI_SPEC_REV, KANI_SPEC_REV, str(self.fx.spec_manifest_path(KANI_SPEC_REV))),
        )
        self.assertEqual(
            report["observed"]["trust_toolchain"]["commit_date"], "2026-09-10"
        )
        self.assertEqual(report["trust"], {"toolchain_override": None})

    # --- Trust toolchain --------------------------------------------------

    def test_trust_commit_hash_mismatch_is_refused(self) -> None:
        self.fx.set_rustc_commit(OTHER_REV)
        self.assertRefusedBy({"trust.commit"}, OTHER_REV, TRUST_REV, "commit-hash")

    def test_rustc_without_commit_hash_is_refused(self) -> None:
        write(self.fx.base / "rustc-vv.txt", "rustc 1.99.0-dev\nbinary: rustc\n")
        self.assertRefusedBy({"trust.commit"}, "reports no commit-hash")

    def test_trust_build_mismatch_is_refused(self) -> None:
        self.fx.set_sysroot(self.fx.base / "store" / "trust" / "6808")
        self.assertRefusedBy({"trust.build"}, "is 6808, but the tuple names 8560")

    def test_unnumbered_sysroot_cannot_confirm_the_build(self) -> None:
        self.fx.set_sysroot(self.fx.base / "rustup" / "toolchains" / "trust")
        self.assertRefusedBy({"trust.build"}, "not a numbered seal directory")

    def _physical_noindex_store(self, name: str = "9192.noindex") -> Path:
        self.fx.tuple["trust"]["build"] = 9192
        self.fx.write_tuple()
        sysroot = self.fx.base / "pkg" / "store" / "trust" / name
        self.fx.set_sysroot(sysroot)
        return sysroot

    def test_physical_native_noindex_build_preserves_full_tuple_checks(self) -> None:
        self._physical_noindex_store()
        report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])
        self.assertEqual(self.fx.check(report, "trust.build")["actual"], "9192")
        self.assertEqual(tuple(check["id"] for check in report["checks"]), tuple_check.CHECK_IDS)

    def test_noindex_build_cannot_rebrand_a_foreign_compiler(self) -> None:
        self._physical_noindex_store()
        self.fx.set_rustc_commit(OTHER_REV)
        self.assertRefusedBy({"trust.commit"}, OTHER_REV, TRUST_REV)

    def test_noindex_store_build_mismatch_is_refused(self) -> None:
        self._physical_noindex_store("9193.noindex")
        self.assertRefusedBy({"trust.build"}, "is 9193, but the tuple names 9192")

    def test_noindex_lookalikes_and_non_store_paths_are_refused(self) -> None:
        for name in ["9192.noindex.extra", "9192.noindex.noindex", "seal-9192.noindex",
                     "x9192.noindex", "09192.noindex", "0.noindex"]:
            with self.subTest(name=name):
                self._physical_noindex_store(name)
                self.assertRefusedBy({"trust.build"}, "not a numbered seal directory")
        self.fx.set_sysroot(self.fx.base / "elsewhere" / "9192.noindex")
        self.assertRefusedBy({"trust.build"}, "not a numbered seal directory")

    def test_noindex_symlink_does_not_become_a_physical_store(self) -> None:
        self._physical_noindex_store("target")
        alias = self.fx.base / "pkg" / "store" / "trust" / "9192.noindex"
        alias.symlink_to(alias.parent / "target", target_is_directory=True)
        write(self.fx.base / "sysroot.txt", f"{alias}\n")
        self.assertRefusedBy({"trust.build"}, "not a numbered seal directory")

    # A VAULTED seal is the same artifact under an archival name. Vaulting is not
    # optional: the aterm store keeps only the newest seals and pruned 8595 — the
    # build the live tuple names — hours after promoting past it. Refusing the
    # vault spelling makes a tuple unverifiable exactly when the store rotates.
    def _vaulted(self, *, reported_commit: str | None) -> Path:
        sysroot = self.fx.base / "seal-vault" / "seal-8560"
        self.fx.set_sysroot(sysroot)
        if reported_commit is not None:
            write(
                sysroot / "PROVENANCE",
                f"provenance_class=BUILD-STAMPED-CLEAN\nreported_commit={reported_commit}\n",
            )
        return sysroot

    def test_vaulted_seal_is_confirmed_by_its_provenance(self) -> None:
        self._vaulted(reported_commit=TRUST_REV)
        report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])
        message = " | ".join(check["message"] for check in report["checks"])
        self.assertIn("VAULTED", message)

    def test_vaulted_seal_with_a_foreign_provenance_is_refused(self) -> None:
        # The name says seal-<build>; PROVENANCE says another compiler. The name
        # must not be enough to claim a build.
        self._vaulted(reported_commit=OTHER_REV)
        self.assertRefusedBy({"trust.build"}, "not the", "this tuple names")

    def test_vaulted_seal_without_provenance_is_refused(self) -> None:
        self._vaulted(reported_commit=None)
        self.assertRefusedBy({"trust.build"}, "no PROVENANCE reported_commit")

    def test_resolver_failure_refuses_commit_and_build(self) -> None:
        write(
            self.fx.root / "scripts" / "resolve-trust-tool.sh",
            "#!/bin/sh\necho 'resolve-trust-tool: error: rustup cannot resolve rustc "
            "for pinned toolchain trust' >&2\nexit 2\n",
            executable=True,
        )
        self.assertRefusedBy(
            {"trust.commit", "trust.build"},
            "rustup cannot resolve rustc for pinned toolchain trust",
            "exited 2",
        )

    def test_trust_channel_mismatch_is_refused(self) -> None:
        write(self.fx.root / "rust-toolchain.toml", '[toolchain]\nchannel = "stable"\n')
        self.assertRefusedBy({"trust.channel"}, "is stable, but the tuple names trust")

    def test_frozen_toolchain_mismatch_is_refused(self) -> None:
        write(
            self.fx.root / "rust-toolchain.legacy.toml",
            '[toolchain]\nchannel = "nightly-2026-08-21"\n',
        )
        self.assertRefusedBy(
            {"frozen.channel"}, "nightly-2026-08-21, but the tuple names nightly-2025-12-03"
        )

    # --- AY ---------------------------------------------------------------

    def test_cargo_toml_ay_pin_mismatch_is_refused(self) -> None:
        write(self.fx.root / "Cargo.toml", ay_manifest(OTHER_REV))
        self.assertRefusedBy(
            {"ay.manifest"}, f"is {OTHER_REV}, but the tuple names {self.fx.ay_rev}"
        )

    def test_non_uniform_ay_pin_is_refused(self) -> None:
        write(
            self.fx.root / "Cargo.toml",
            ay_manifest(self.fx.ay_rev, odd_one_out=OTHER_REV),
        )
        self.assertRefusedBy({"ay.manifest"}, "not one exact pin", "must use one revision")

    def test_ay_checkout_head_mismatch_is_refused(self) -> None:
        write(self.fx.ay / "later.txt", "moved on\n")
        moved = commit_all(self.fx.ay)
        self.assertRefusedBy(
            {"ay.checkout"}, f"HEAD is {moved}, but the tuple names {self.fx.ay_rev}"
        )

    def test_dirty_ay_checkout_is_refused(self) -> None:
        write(self.fx.ay / "scratch.txt", "untracked\n")
        report = self.assertRefusedBy({"ay.checkout"}, "but dirty", "scratch.txt")
        self.assertEqual(
            self.fx.check(report, "ay.checkout")["actual"], f"{self.fx.ay_rev}-dirty"
        )

    def test_missing_ay_checkout_is_refused(self) -> None:
        shutil.rmtree(self.fx.ay)
        self.assertRefusedBy({"ay.checkout"}, "does not exist")

    # --- TrustIR, trust-vc, Clean ------------------------------------------

    def test_trust_ir_declaration_mismatch_is_refused(self) -> None:
        write(
            self.fx.root / "member" / "Cargo.toml",
            member_manifest(OTHER_REV, TRUST_VC_REV),
        )
        self.assertRefusedBy({"trust-ir.manifest"}, "TrustIR revision", OTHER_REV)

    def test_trust_ir_checkout_mismatch_is_refused(self) -> None:
        write(self.fx.trust_ir / "later.txt", "moved on\n")
        commit_all(self.fx.trust_ir)
        self.assertRefusedBy({"trust-ir.checkout"}, "TrustIR checkout")

    def test_trust_vc_declaration_mismatch_is_refused(self) -> None:
        write(
            self.fx.root / "member" / "Cargo.toml",
            member_manifest(self.fx.trust_ir_rev, OTHER_REV),
        )
        self.assertRefusedBy({"trust-vc.manifest"}, "trust-vc revision", OTHER_REV)

    def test_trust_vc_lock_mismatch_is_refused(self) -> None:
        write(self.fx.root / "Cargo.lock", lockfile(CLEAN_REV, OTHER_REV))
        self.assertRefusedBy(
            {"trust-vc.lock"}, "trust-vc-merge-contract commit Cargo.lock resolves", OTHER_REV
        )

    def test_clean_declaration_mismatch_is_refused(self) -> None:
        self.fx.tuple["clean"]["rev"] = OTHER_REV
        self.fx.write_tuple()
        self.assertRefusedBy(
            {"clean.manifest", "clean.lock"},
            "Clean revision",
            f"is {CLEAN_REV}, but the tuple names {OTHER_REV}",
        )

    def test_clean_lock_mismatch_is_refused(self) -> None:
        write(self.fx.root / "Cargo.lock", lockfile(OTHER_REV, TRUST_VC_REV))
        self.assertRefusedBy({"clean.lock"}, "clean-kernel commit Cargo.lock resolves")

    def test_trust_ir_checkout_clean_declaration_mismatch_is_refused(self) -> None:
        # The tuple and Cargo.lock still name CLEAN_REV; only ../trust-ir moved.
        write(self.fx.trust_ir / "Cargo.toml", clean_manifest(OTHER_REV))
        moved = commit_all(self.fx.trust_ir)
        write(self.fx.root / "member" / "Cargo.toml", member_manifest(moved, TRUST_VC_REV))
        self.fx.tuple["trust_ir"]["rev"] = moved
        self.fx.write_tuple()
        self.assertRefusedBy(
            {"clean.manifest"},
            "Clean revision",
            f"is {OTHER_REV}, but the tuple names {CLEAN_REV}",
        )

    def test_missing_trust_ir_checkout_is_refused(self) -> None:
        shutil.rmtree(self.fx.trust_ir)
        self.assertRefusedBy({"trust-ir.checkout", "clean.manifest"}, "does not exist")

    def test_lock_request_and_commit_disagreement_is_refused(self) -> None:
        text = lockfile(CLEAN_REV, TRUST_VC_REV).replace(
            f"?rev={CLEAN_REV}#{CLEAN_REV}", f"?rev={CLEAN_REV}#{OTHER_REV}"
        )
        write(self.fx.root / "Cargo.lock", text)
        self.assertRefusedBy({"clean.lock"}, "but locks commit")

    # --- Kani -------------------------------------------------------------

    def test_kani_corpus_rev_mismatch_is_refused(self) -> None:
        write(
            self.fx.root / "tools" / "kani-domination" / "src" / "clone.rs",
            clone_rs(OTHER_REV),
        )
        self.assertRefusedBy(
            {"kani.corpus"}, f"DEFAULT_KANI_REV is {OTHER_REV}, but the tuple names"
        )

    def test_missing_kani_corpus_declaration_is_refused(self) -> None:
        write(
            self.fx.root / "tools" / "kani-domination" / "src" / "clone.rs",
            "pub fn clone_kani() {}\n",
        )
        self.assertRefusedBy({"kani.corpus"}, "exactly once; found 0")

    def test_kani_corpus_pin_mismatch_is_refused(self) -> None:
        write(self.fx.pins_path, kani_spec_pins(OTHER_REV, KANI_SPEC_REV))
        self.assertRefusedBy(
            {"kani.corpus"},
            f"[revs.corpus] rev = {OTHER_REV}, but the tuple's [kani] corpus_rev is "
            f"{self.fx.kani_rev}",
        )

    def test_missing_kani_corpus_manifest_is_refused(self) -> None:
        self.fx.spec_manifest_path(self.fx.kani_rev).unlink()
        self.assertRefusedBy(
            {"kani.corpus"},
            f"{self.fx.spec_manifest_path(self.fx.kani_rev)} does not exist",
        )

    def test_kani_spec_pin_mismatch_is_refused(self) -> None:
        write(self.fx.pins_path, kani_spec_pins(self.fx.kani_rev, OTHER_REV))
        write(self.fx.spec_manifest_path(OTHER_REV), spec_manifest(OTHER_REV))
        report = self.assertRefusedBy(
            {"kani.spec"},
            f"[revs.spec] rev = {OTHER_REV}, but the tuple's [kani] spec_rev is {KANI_SPEC_REV}",
        )
        check = self.fx.check(report, "kani.spec")
        self.assertEqual((check["expected"], check["actual"]), (KANI_SPEC_REV, OTHER_REV))

    def test_kani_spec_tuple_rev_without_a_matching_pin_is_refused(self) -> None:
        self.fx.tuple["kani"]["spec_rev"] = OTHER_REV
        self.fx.write_tuple()
        self.assertRefusedBy(
            {"kani.spec"},
            f"[revs.spec] rev = {KANI_SPEC_REV}, but the tuple's [kani] spec_rev is {OTHER_REV}",
        )

    def test_missing_kani_spec_manifest_is_refused(self) -> None:
        manifest = self.fx.spec_manifest_path(KANI_SPEC_REV)
        manifest.unlink()
        report = self.assertRefusedBy(
            {"kani.spec"}, f"the generated spec manifest {manifest} does not exist"
        )
        self.assertEqual(report["unchecked"], [])

    def test_kani_spec_manifest_rev_mismatch_is_refused(self) -> None:
        manifest = self.fx.spec_manifest_path(KANI_SPEC_REV)
        write(manifest, spec_manifest(OTHER_REV))
        report = self.assertRefusedBy(
            {"kani.spec"},
            f"{manifest} records kani_rev {OTHER_REV}, but pins.toml [revs.spec] "
            f"and the tuple's [kani] spec_rev name {KANI_SPEC_REV}",
        )
        check = self.fx.check(report, "kani.spec")
        self.assertEqual((check["actual"], check["source"]), (OTHER_REV, str(manifest)))

    def test_kani_spec_manifest_without_kani_rev_is_refused(self) -> None:
        write(self.fx.spec_manifest_path(KANI_SPEC_REV), "{}\n")
        self.assertRefusedBy({"kani.spec"}, "has no kani_rev string")

    def test_missing_kani_spec_pins_refuses_corpus_and_spec(self) -> None:
        self.fx.pins_path.unlink()
        self.assertRefusedBy({"kani.corpus", "kani.spec"}, "pins.toml does not exist")

    def test_pins_without_a_spec_entry_refuses_spec(self) -> None:
        pins = kani_spec_pins(self.fx.kani_rev, KANI_SPEC_REV)
        write(self.fx.pins_path, pins[: pins.index("[revs.spec]")])
        report = self.assertRefusedBy({"kani.spec"}, "must pin [revs.spec] rev", "found None")
        self.assertEqual(report["unchecked"], [])

    def test_zero_spec_pin_is_refused(self) -> None:
        write(self.fx.pins_path, kani_spec_pins(self.fx.kani_rev, "0" * 40))
        self.assertRefusedBy({"kani.spec"}, "must pin [revs.spec] rev as a nonzero")

    def test_other_revs_manifest_under_the_pinned_directory_is_refused(self) -> None:
        manifest = self.fx.spec_manifest_path(KANI_SPEC_REV)
        write(manifest, self.fx.spec_manifest_path(self.fx.kani_rev).read_text())
        self.assertRefusedBy(
            {"kani.spec"}, f"{manifest} records kani_rev {self.fx.kani_rev}"
        )

    def test_manifest_with_a_duplicated_kani_rev_is_refused(self) -> None:
        manifest = self.fx.spec_manifest_path(KANI_SPEC_REV)
        write(manifest, f'{{"kani_rev": "{OTHER_REV}", "kani_rev": "{KANI_SPEC_REV}"}}\n')
        self.assertRefusedBy({"kani.spec"}, f"{manifest} repeats the key(s) kani_rev")

    def test_spec_rev_that_is_a_prefix_of_the_pin_is_a_usage_error(self) -> None:
        self.fx.tuple["kani"]["spec_rev"] = KANI_SPEC_REV[:12]
        self.fx.write_tuple()
        with self.assertRaisesRegex(tuple_check.TupleError, r"kani\.spec_rev must be a nonzero"):
            self.fx.report()

    def test_kani_checkout_head_mismatch_is_refused(self) -> None:
        # The declaration still matches; the corpus on disk does not.
        write(self.fx.kani / "tests" / "kani" / "later.rs", "fn later() {}\n")
        moved = commit_all(self.fx.kani)
        self.assertRefusedBy(
            {"kani.checkout"}, f"HEAD is {moved}, but the tuple names {self.fx.kani_rev}"
        )

    def test_kani_checkout_with_edited_tracked_file_is_refused(self) -> None:
        write(self.fx.kani / "tests" / "kani" / "harness.rs", "fn main() { panic!() }\n")
        self.assertRefusedBy({"kani.checkout"}, "but dirty", "harness.rs")

    def test_kani_checkout_untracked_run_artifacts_do_not_count(self) -> None:
        write(self.fx.kani / "tests" / "expected" / "t.symtab.smt2", "(check-sat)\n")
        report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])

    def test_kani_checkout_is_the_corpus_dir_the_runner_is_told_about(self) -> None:
        report = self.fx.report()
        self.assertEqual(self.fx.check(report, "kani.checkout")["source"], str(self.fx.kani))

    def test_kani_checkout_defaults_to_the_per_rev_user_cache(self) -> None:
        home = self.fx.base / "home"
        cache = home / "Library" / "Caches" if sys.platform == "darwin" else home / ".cache"
        corpus = cache / "trust-mc" / "kani-domination" / self.fx.kani_rev
        corpus.parent.mkdir(parents=True)
        shutil.move(str(self.fx.kani), str(corpus))
        self._without_corpus_override(HOME=str(home))
        report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])
        check = self.fx.check(report, "kani.checkout")
        self.assertEqual((check["status"], check["source"]), ("pass", str(corpus)))

    def test_a_corpus_left_under_target_is_not_read(self) -> None:
        # The location before 2026-09-11: kani-domination no longer reads it,
        # so a clean checkout there must not satisfy kani.checkout.
        stale = self.fx.root / "target" / "kani-domination" / "kani"
        stale.parent.mkdir(parents=True)
        shutil.move(str(self.fx.kani), str(stale))
        home = self.fx.base / "empty-home"
        home.mkdir()
        self._without_corpus_override(HOME=str(home))
        report = self.fx.report()
        self.assertEqual(report["unchecked"], ["kani.checkout"])
        self.assertNotIn("target", self.fx.check(report, "kani.checkout")["source"])

    def test_kani_checkout_keyed_by_another_rev_is_not_this_tuples(self) -> None:
        # The runner keys the default checkout by DEFAULT_KANI_REV; one cloned
        # for another rev sits elsewhere and does not count.
        home = self.fx.base / "home"
        cache = home / "Library" / "Caches" if sys.platform == "darwin" else home / ".cache"
        elsewhere = cache / "trust-mc" / "kani-domination" / OTHER_REV
        elsewhere.parent.mkdir(parents=True)
        shutil.move(str(self.fx.kani), str(elsewhere))
        self._without_corpus_override(HOME=str(home))
        report = self.fx.report()
        self.assertEqual(report["unchecked"], ["kani.checkout"])

    def test_absent_kani_checkout_is_unchecked_not_passed(self) -> None:
        shutil.rmtree(self.fx.kani)
        report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])
        self.assertEqual(report["unchecked"], ["kani.checkout"])
        self.assertIn("does not exist yet", self.fx.check(report, "kani.checkout")["message"])

    # --- the tuple file ---------------------------------------------------

    def test_short_revision_in_tuple_is_a_usage_error(self) -> None:
        self.fx.tuple["ay"]["rev"] = "94bf24d0f"
        self.fx.write_tuple()
        with self.assertRaisesRegex(tuple_check.TupleError, r"ay\.rev must be a nonzero"):
            self.fx.report()

    def test_unknown_or_missing_tuple_fields_are_rejected(self) -> None:
        self.fx.tuple["trust"]["commit"] = TRUST_REV
        del self.fx.tuple["kani"]["spec_rev"]
        self.fx.write_tuple()
        with self.assertRaises(tuple_check.TupleError) as raised:
            self.fx.report()
        self.assertIn("unknown key trust.commit", str(raised.exception))
        self.assertIn("kani.spec_rev must be", str(raised.exception))

    def test_boolean_build_is_rejected(self) -> None:
        self.fx.tuple["trust"]["build"] = True
        self.fx.write_tuple()
        with self.assertRaisesRegex(tuple_check.TupleError, "positive integer seal build"):
            self.fx.report()

    # --- command line -----------------------------------------------------

    def _cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(CHECKER), "--repo-root", str(self.fx.root), *args],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_cli_json_reports_pass_and_failure_with_exit_codes(self) -> None:
        passed = self._cli("--json")
        self.assertEqual(passed.returncode, 0, passed.stderr)
        self.assertTrue(json.loads(passed.stdout)["ok"])
        self.assertEqual(passed.stderr, "")

        self.fx.set_rustc_commit(OTHER_REV)
        failed = self._cli("--json")
        self.assertEqual(failed.returncode, 1)
        report = json.loads(failed.stdout)
        self.assertEqual(report["failed"], ["trust.commit"])
        self.assertEqual(report["schema"], tuple_check.REPORT_SCHEMA)
        self.assertIn("tuple-check: error: trust.commit:", failed.stderr)

    def test_cli_text_names_each_refusal(self) -> None:
        write(self.fx.ay / "scratch.txt", "untracked\n")
        self.fx.set_rustc_commit(OTHER_REV)
        result = self._cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("tuple-check: error: trust.commit:", result.stderr)
        self.assertIn("tuple-check: error: ay.checkout:", result.stderr)
        self.assertIn("2 of 15 checks refuse", result.stderr)
        self.assertIn("tuple-check: ok: kani.spec:", result.stdout)

    def test_cli_malformed_tuple_exits_two_with_json_error(self) -> None:
        write(self.fx.tuple_path, "schema = 1\n[trust\n")
        result = self._cli("--json")
        self.assertEqual(result.returncode, 2)
        self.assertIn("not valid TOML", json.loads(result.stdout)["error"])

    def test_wrapper_resolves_a_tomllib_python(self) -> None:
        result = subprocess.run(
            [str(WRAPPER), "--help"], capture_output=True, text=True, check=False
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--json", result.stdout)

    def test_wrapper_without_a_tomllib_python_exits_two_not_one(self) -> None:
        # 1 means "tuple mismatch"; a missing interpreter must not look like one.
        with tempfile.TemporaryDirectory() as bin_dir:
            bin_path = Path(bin_dir)
            (bin_path / "dirname").symlink_to(shutil.which("dirname"))
            write(bin_path / "python3", "#!/bin/sh\nexit 1\n", executable=True)
            env = {
                key: value
                for key, value in os.environ.items()
                if key not in ("AY_PYTHON", "AY_PYTHON_BIN")
            }
            env["PATH"] = bin_dir
            result = subprocess.run(
                ["/bin/bash", str(WRAPPER), "--json"],
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("no python3 with tomllib", result.stderr)


class ToolchainOverrideTests(unittest.TestCase):
    """TRUST_MC_TRUST_TOOLCHAIN through the real scripts/resolve-trust-tool.sh.

    rustup's `trust` channel resolves to seal 8571, which the tuple does not
    name; the tuple's build 8560 is reachable only through the override, as a
    rustup toolchain (trust-8560) or as its absolute seal directory.
    """

    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.fx = Fixture(Path(self._temporary.name).resolve())
        shutil.copy2(
            ROOT / "scripts" / "resolve-trust-tool.sh",
            self.fx.root / "scripts" / "resolve-trust-tool.sh",
        )
        store = self.fx.base / "Application Support" / "store" / "trust"
        self.moved_seal = self.seal(store / "8571", OTHER_REV)
        self.tuple_seal = self.seal(store / "8560", TRUST_REV)
        rustup = self.fx.base / "rustup-bin" / "rustup"
        write(
            rustup,
            "#!/bin/sh\n"
            '[ "$1 $2 $3" = "which rustc --toolchain" ] || exit 3\n'
            'case "$4" in\n'
            f"  trust) printf '%s\\n' '{self.moved_seal / 'bin' / 'rustc'}' ;;\n"
            f"  trust-8560) printf '%s\\n' '{self.tuple_seal / 'bin' / 'rustc'}' ;;\n"
            "  *) echo \"error: toolchain '$4' is not installed\" >&2; exit 1 ;;\n"
            "esac\n",
            executable=True,
        )
        environment = mock.patch.dict(
            os.environ,
            {
                tuple_check.KANI_CORPUS_DIR_ENV: str(self.fx.kani),
                "TRUST_MC_RUSTUP": str(rustup),
            },
        )
        environment.start()
        self.addCleanup(environment.stop)
        os.environ.pop(tuple_check.TRUST_TOOLCHAIN_OVERRIDE_ENV, None)

    def seal(self, directory: Path, commit: str) -> Path:
        write(
            directory / "rustc-vv.txt",
            f"rustc 1.99.0-dev ({commit[:9]} 2026-09-10)\nbinary: rustc\n"
            f"commit-hash: {commit}\ncommit-date: 2026-09-10\n",
        )
        # The seal's compiler under both names, as a real seal ships it: rustup
        # resolves `rustc`, the checker runs `trustc`. No `cargo` is needed.
        for name in ("rustc", "trustc"):
            write(
                directory / "bin" / name,
                "#!/bin/sh\n"
                'case "$1" in\n'
                f"  -Vv) cat '{directory / 'rustc-vv.txt'}' ;;\n"
                f"  --print) printf '%s\\n' '{directory}' ;;\n"
                "  *) exit 2 ;;\n"
                "esac\n",
                executable=True,
            )
        write(directory / "bin" / "targo", "#!/bin/sh\nexit 0\n", executable=True)
        return directory

    def override(self, value: str) -> None:
        os.environ[tuple_check.TRUST_TOOLCHAIN_OVERRIDE_ENV] = value

    def trust_checks(self, report: dict) -> dict[str, dict]:
        return {
            check_id: self.fx.check(report, check_id)
            for check_id in ("trust.commit", "trust.build")
        }

    def test_unset_override_resolves_the_moved_channel_and_records_null(self) -> None:
        report = self.fx.report()
        self.assertEqual(set(report["failed"]), {"trust.commit", "trust.build"})
        checks = self.trust_checks(report)
        self.assertEqual(checks["trust.commit"]["actual"], OTHER_REV)
        self.assertEqual(checks["trust.build"]["actual"], "8571")
        self.assertIn("is 8571, but the tuple names 8560", checks["trust.build"]["message"])
        self.assertEqual(report["trust"], {"toolchain_override": None})
        self.assertNotIn("TRUST_MC_TRUST_TOOLCHAIN", json.dumps(report["checks"]))

    def test_override_holds_the_tuple_build_as_seal_directory_or_rustup_name(self) -> None:
        for value in (str(self.tuple_seal), "trust-8560"):
            with self.subTest(override=value):
                self.override(value)
                report = self.fx.report()
                self.assertTrue(report["ok"], report["checks"])
                checks = self.trust_checks(report)
                self.assertEqual(
                    (checks["trust.commit"]["actual"], checks["trust.build"]["actual"]),
                    (TRUST_REV, "8560"),
                )
                for check in checks.values():
                    self.assertIn(f"TRUST_MC_TRUST_TOOLCHAIN={value}", check["message"])
                self.assertEqual(
                    report["observed"]["trust_toolchain"]["sysroot"], str(self.tuple_seal)
                )
                self.assertEqual(report["trust"], {"toolchain_override": value})

    def test_override_naming_another_build_is_compared_not_trusted(self) -> None:
        self.override(str(self.moved_seal))
        report = self.fx.report()
        self.assertEqual(set(report["failed"]), {"trust.commit", "trust.build"})
        self.assertEqual(self.trust_checks(report)["trust.build"]["actual"], "8571")
        self.assertEqual(report["trust"], {"toolchain_override": str(self.moved_seal)})

    def test_unresolvable_override_refuses_commit_and_build(self) -> None:
        cases = {
            "trust-0000": "rustup cannot resolve rustc for TRUST_MC_TRUST_TOOLCHAIN=trust-0000",
            str(self.fx.base / "store" / "trust" / "9999"): "names no directory",
            "store/trust/8560": "neither a rustup toolchain name nor an absolute seal directory",
            "": "is set but empty",
        }
        for value, fragment in cases.items():
            with self.subTest(override=value):
                self.override(value)
                report = self.fx.report()
                self.assertFalse(report["ok"])
                self.assertEqual(set(report["failed"]), {"trust.commit", "trust.build"})
                for check in self.trust_checks(report).values():
                    self.assertIsNone(check["actual"])
                    self.assertIn(fragment, check["message"])
                self.assertEqual(report["trust"], {"toolchain_override": value})

    def test_cli_records_the_override_in_json_and_notes_it_in_text(self) -> None:
        self.override(str(self.tuple_seal))
        command = [sys.executable, str(CHECKER), "--repo-root", str(self.fx.root)]
        as_json = subprocess.run(
            [*command, "--json"], capture_output=True, text=True, check=False
        )
        self.assertEqual(as_json.returncode, 0, as_json.stderr)
        report = json.loads(as_json.stdout)
        self.assertEqual(report["trust"]["toolchain_override"], str(self.tuple_seal))
        as_text = subprocess.run(command, capture_output=True, text=True, check=False)
        self.assertEqual(as_text.returncode, 0, as_text.stderr)
        self.assertIn(
            f"tuple-check: note: TRUST_MC_TRUST_TOOLCHAIN={self.tuple_seal} selects",
            as_text.stdout,
        )


class DevelopmentTupleTests(unittest.TestCase):
    """Explicit schema2 integrates a synthetic seal without invoking a compiler."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.fx = Fixture(Path(temporary.name).resolve())
        self.seal = SealFixture(self.fx.base / "development", TRUST_REV)
        self.fx.tuple["schema"] = 2
        self.fx.tuple["trust"] = {"rev": TRUST_REV, "channel": "trust", "identity": "development"}
        self.fx.tuple["development_seal"] = self.seal.table
        self.fx.write_tuple()
        self.probe = tuple_check.ToolchainProbe(
            rustc=str(self.seal.root / "bin/trustc"),
            sysroot=str(self.seal.root),
            verbose={"commit-hash": TRUST_REV, "host": DEVELOPMENT_HOST},
        )
        environment = mock.patch.dict(os.environ, {tuple_check.KANI_CORPUS_DIR_ENV: str(self.fx.kani)})
        environment.start()
        self.addCleanup(environment.stop)
        os.environ.pop(tuple_check.TRUST_TOOLCHAIN_OVERRIDE_ENV, None)
        probe = mock.patch.object(tuple_check, "probe_trust_toolchain", return_value=self.probe)
        probe.start()
        self.addCleanup(probe.stop)

    def test_explicit_development_tuple_passes_with_limited_report(self) -> None:
        result = self.fx.report()
        self.assertTrue(result["ok"], result["checks"])
        self.assertEqual(result["schema"], 2)
        self.assertEqual(result["trust"]["identity_classification"], "development")
        self.assertTrue(result["trust"]["development_identity_established"])
        identity = result["trust"]["development_identity"]
        self.assertEqual(identity["compiler_commit"], TRUST_REV)
        self.assertEqual(identity["build_stamp_scope"], "top-level source state only")
        self.assertIn("no complete sysroot authentication", result["trust"]["identity_scope"])
        self.assertIsNone(result["observed"]["trust_toolchain"]["seal_provenance"])
        self.assertEqual(tuple(check["id"] for check in result["checks"]), tuple_check.CHECK_IDS)

    def test_cli_default_schema2_refuses_before_probing(self) -> None:
        with mock.patch.object(tuple_check, "probe_trust_toolchain") as probe, mock.patch("sys.stderr", new_callable=io.StringIO) as stderr:
            status = tuple_check.main(["--repo-root", str(self.fx.root)])
        self.assertEqual(status, 2)
        probe.assert_not_called()
        self.assertIn("requires explicit --tuple", stderr.getvalue())

    def test_cli_explicit_schema2_selection_is_reported_as_development(self) -> None:
        with mock.patch("sys.stdout", new_callable=io.StringIO) as stdout:
            status = tuple_check.main(["--repo-root", str(self.fx.root), "--tuple", str(self.fx.tuple_path), "--json"])
        self.assertEqual(status, 0)
        self.assertEqual(json.loads(stdout.getvalue())["trust"]["identity_classification"], "development")

    def test_report_digest_is_of_captured_tuple_bytes_despite_later_edit(self) -> None:
        original_bytes = self.fx.tuple_path.read_bytes()
        run_checks = tuple_check.run_checks

        def modify_after_checks(*args: object) -> tuple:
            result = run_checks(*args)
            self.fx.tuple_path.write_bytes(original_bytes + b"# modified after parsing\n")
            return result

        with mock.patch.object(tuple_check, "run_checks", side_effect=modify_after_checks):
            report = self.fx.report()
        self.assertTrue(report["ok"], report["checks"])
        self.assertEqual(report["tuple_sha256"], hashlib.sha256(original_bytes).hexdigest())
        self.assertNotEqual(report["tuple_sha256"], hashlib.sha256(self.fx.tuple_path.read_bytes()).hexdigest())

    def test_committed_numbered_tuple_refuses_same_commit_development_seal(self) -> None:
        committed = tuple_check.load_tuple(ROOT / "tools/tuple.toml")
        self.assertEqual(committed.document["schema"], 1)
        self.assertIsInstance(committed.trust_build, int)
        self.assertGreater(committed.trust_build, 0)
        self.fx.tuple["schema"] = 1
        self.fx.tuple["trust"] = {"rev": committed.trust_rev, "channel": "trust", "build": committed.trust_build}
        del self.fx.tuple["development_seal"]
        self.fx.write_tuple()
        # Matching compiler source does not turn an unnumbered development
        # sysroot into the committed numbered seal. Keep this independent of
        # whichever seal the real tuple currently pins.
        self.probe.verbose["commit-hash"] = committed.trust_rev
        result = self.fx.report()
        self.assertEqual(set(result["failed"]), {"trust.build"})
        self.assertEqual(result["schema"], 1)
        self.assertEqual(result["trust"], {"toolchain_override": None})
        self.assertIn("not a numbered seal", self.fx.check(result, "trust.build")["message"])

    def test_schema1_never_auto_selects_development_identity(self) -> None:
        self.fx.tuple["schema"] = 1
        self.fx.tuple["trust"] = {"rev": TRUST_REV, "channel": "trust", "build": 8560}
        self.fx.write_tuple()
        with self.assertRaisesRegex(tuple_check.TupleError, "unknown top-level key 'development_seal'"):
            tuple_check.load_tuple(self.fx.tuple_path)

    def test_schema2_mixed_numbered_identity_and_unknown_fields_refuse(self) -> None:
        for table, key, value in (
            ("trust", "build", 9192), ("trust", "identity", "release"),
            ("development_seal", "extra", "ignored"), ("development_seal", "driver_bytes", True),
        ):
            original = dict(self.fx.tuple[table])
            with self.subTest(table=table, key=key):
                self.fx.tuple[table][key] = value
                self.fx.write_tuple()
                try:
                    with self.assertRaises(tuple_check.TupleError):
                        tuple_check.load_tuple(self.fx.tuple_path)
                finally:
                    self.fx.tuple[table] = original

    def test_schema2_missing_contract_refuses(self) -> None:
        del self.fx.tuple["development_seal"]
        self.fx.write_tuple()
        with self.assertRaisesRegex(tuple_check.TupleError, "development_seal"):
            tuple_check.load_tuple(self.fx.tuple_path)

    def test_mismatch_does_not_emit_an_established_development_identity(self) -> None:
        self.probe.sysroot = str(self.fx.base / "other")
        result = self.fx.report()
        self.assertEqual(result["failed"], ["trust.build"])
        self.assertFalse(result["trust"]["development_identity_established"])
        self.assertIsNone(result["trust"]["development_identity"])

    def test_artifact_tamper_refuses_only_development_build_identity(self) -> None:
        (self.seal.root / "bin/targo").write_bytes(b"tampered")
        result = self.fx.report()
        self.assertEqual(result["failed"], ["trust.build"])
        self.assertFalse(result["trust"]["development_identity_established"])


class CommittedTupleTests(unittest.TestCase):
    """The committed tuple agrees with every declaration inside this tree.

    Host-independent: nothing here reads a sibling checkout or a toolchain, so a
    bump that moves a pin without moving tools/tuple.toml fails on any host.
    """

    def test_committed_tuple_is_well_formed(self) -> None:
        tuple_check.load_tuple(ROOT / "tools" / "tuple.toml")

    def test_committed_tuple_matches_in_tree_declarations(self) -> None:
        committed = tuple_check.load_tuple(ROOT / "tools" / "tuple.toml")
        layout = tuple_check.Layout(ROOT)
        checks = [
            tuple_check.check_trust_channel(layout, committed),
            tuple_check.check_frozen_channel(layout, committed),
            tuple_check.check_ay_manifest(layout, committed),
            tuple_check.check_trust_ir_manifest(layout, committed),
            tuple_check.check_trust_vc_manifest(layout, committed),
            tuple_check.check_trust_vc_lock(layout, committed),
            tuple_check.check_clean_lock(layout, committed),
            tuple_check.check_kani_corpus(layout, committed),
            tuple_check.check_kani_spec(layout, committed),
        ]
        for check in checks:
            with self.subTest(check=check.id):
                self.assertEqual(check.status, tuple_check.PASS, check.message)


if __name__ == "__main__":
    unittest.main()
