#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Pure synthetic admission tests; no toolchain execution or sibling mutation."""

from __future__ import annotations

import hashlib
import os
import shutil
import tempfile
import unittest
from pathlib import Path
from typing import Callable
from unittest import mock

import development_seal as ds

REV = "a" * 40
HOST = "aarch64-unknown-linux-gnu"


class SealFixture:
    def __init__(self, root: Path, revision: str = REV) -> None:
        self.root = root
        self.revision = revision
        root.mkdir(parents=True, mode=0o700)
        (root / "bin").mkdir(parents=True, mode=0o700)
        (root / "lib").mkdir(mode=0o700)
        self.table = {"root": str(root), "host": HOST}
        for role, path in (("trustc", "bin/trustc"), ("targo", "bin/targo"), ("driver", "lib/librustc_driver-test.so")):
            raw = (role + " synthetic artifact\n").encode()
            (root / path).write_bytes(raw)
            (root / path).chmod(0o755)
            self.table[role + "_sha256"] = hashlib.sha256(raw).hexdigest()
            self.table[role + "_bytes"] = len(raw)
        self.table["driver_path"] = "lib/librustc_driver-test.so"
        empty = hashlib.sha256(b"").hexdigest()
        self.fields = {
            "provenance_class": "BUILD-STAMPED-CLEAN", "seal_name": root.name,
            "reported_commit": revision, "reported_rev": revision[:9],
            "artifact_driver_name": "librustc_driver-test.so",
            "artifact_driver_sha256": self.table["driver_sha256"],
            "artifact_driver_bytes": str(self.table["driver_bytes"]),
            "artifact_bin_trustc_sha256": self.table["trustc_sha256"],
            "artifact_bin_targo_sha256": self.table["targo_sha256"],
            "sealtime_repo_head": revision, "sealtime_repo_tree": "clean",
            "sealtime_head_matches_binary": "yes", "build_stamp:record_version": "1",
            "build_stamp:record_kind": "build-stamp", "build_stamp:head": revision,
            "build_stamp:tree_state": "clean", "build_stamp:dirty_tracked": "0",
            "build_stamp:dirty_untracked": "0", "build_stamp:exit_status": "ok",
            "build_stamp:tree_changed_during_build": "no",
            "build_stamp:diff_sha256": empty, "build_stamp:status_sha256": empty,
            "build_stamp:submodule_sha256": hashlib.sha256(b"synthetic submodule status\n").hexdigest(),
            "build_stamp:started_at": "1700000000", "build_stamp:completed_at": "1700000010",
        }
        material = "".join(self.fields["build_stamp:" + key] + "\n" for key in (
            "head", "diff_sha256", "status_sha256", "submodule_sha256",
        ))
        fingerprint = hashlib.sha256(material.encode()).hexdigest()
        self.fields["build_stamp:tree_fingerprint"] = fingerprint
        self.fields["build_stamp:end_tree_fingerprint"] = fingerprint
        self.write_provenance()

    def write_provenance(self, extra: bytes = b"") -> None:
        raw = "".join(f"{key}={value}\n" for key, value in self.fields.items()).encode() + extra
        (self.root / "PROVENANCE").write_bytes(raw)
        (self.root / "PROVENANCE").chmod(0o600)
        self.table["provenance_sha256"] = hashlib.sha256(raw).hexdigest()

    @property
    def seal(self) -> ds.DevelopmentSeal:
        return ds.DevelopmentSeal.parse(self.table)

    def verify(self, **kwargs: object) -> dict:
        options = {
            "observed_sysroot": str(self.root),
            "observed_compiler": str(self.root / "bin/trustc"),
            "verbose": {"commit-hash": self.revision, "host": HOST},
        }
        options.update(kwargs)
        return ds.verify(self.seal, self.revision, **options)


class DevelopmentSealTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.fx = SealFixture(self.base / "development")

    def test_exact_identity_is_development_and_stamp_is_top_level_only(self) -> None:
        self.fx.write_provenance(b"build_stamp:# copied original stamp comment\n")
        result = self.fx.verify()
        self.assertEqual(result["classification"], "development")
        self.assertEqual(result["build_stamp_scope"], "top-level source state only")
        self.assertIn("no complete sysroot authentication", result["scope"])
        self.assertEqual([item["path"] for item in result["artifacts"]], ["bin/trustc", "bin/targo", self.fx.table["driver_path"]])

    def test_owner_writable_product_aliases_are_accounted(self) -> None:
        os.link(self.fx.root / "bin/trustc", self.fx.root / "bin/rustc")
        os.link(self.fx.root / "bin/targo", self.fx.root / "bin/cargo")
        nested = self.fx.root / "lib/rustlib/native/lib"
        nested.mkdir(parents=True)
        for directory in (nested, nested.parent, nested.parent.parent):
            directory.chmod(0o755)
        os.link(self.fx.root / self.fx.table["driver_path"], nested / "librustc_driver-test.so")
        result = self.fx.verify()
        self.assertEqual(result["artifacts"][0]["aliases"], ["bin/rustc", "bin/trustc"])
        self.assertEqual(len(result["artifacts"][2]["aliases"]), 2)

    def test_external_critical_hardlink_refuses(self) -> None:
        os.link(self.fx.root / "bin/trustc", self.base / "external")
        with self.assertRaisesRegex(ds.SealRefusal, "external hardlinks"):
            self.fx.verify()

    def test_external_provenance_hardlink_refuses(self) -> None:
        os.link(self.fx.root / "PROVENANCE", self.base / "external")
        with self.assertRaisesRegex(ds.SealRefusal, "external hardlinks"):
            self.fx.verify()

    def test_internal_aliases_remain_finitely_bounded(self) -> None:
        os.link(self.fx.root / "bin/trustc", self.fx.root / "bin/rustc")
        with mock.patch.object(ds, "MAX_CRITICAL_ALIASES", 1):
            with self.assertRaisesRegex(ds.SealRefusal, "hardlink bound"):
                self.fx.verify()

    def test_group_or_other_writes_refuse_on_all_admitted_owners(self) -> None:
        for relative in ("", "bin", "lib", "PROVENANCE", "bin/trustc", "bin/targo", self.fx.table["driver_path"]):
            path = self.fx.root / relative
            original = path.stat().st_mode & 0o777
            for permission in (0o020, 0o002):
                with self.subTest(relative=relative, permission=permission):
                    path.chmod(original | permission)
                    try:
                        with self.assertRaisesRegex(ds.SealRefusal, "group/other write"):
                            self.fx.verify()
                    finally:
                        path.chmod(original)

    def test_foreign_owner_refuses(self) -> None:
        with mock.patch.object(ds.os, "geteuid", return_value=os.geteuid() + 1):
            with self.assertRaisesRegex(ds.SealRefusal, "owned by this user"):
                self.fx.verify()

    def test_symlink_critical_input_refuses(self) -> None:
        path = self.fx.root / "bin/trustc"
        path.rename(self.base / "compiler")
        path.symlink_to(self.base / "compiler")
        with self.assertRaises(ds.SealRefusal):
            self.fx.verify()

    def test_symlink_ancestor_and_root_refuse(self) -> None:
        alias = self.base / "alias"
        alias.symlink_to(self.base, target_is_directory=True)
        self.fx.table["root"] = str(alias / self.fx.root.name)
        with self.assertRaises(ds.SealRefusal):
            self.fx.verify(observed_sysroot=self.fx.table["root"], observed_compiler=self.fx.table["root"] + "/bin/trustc")

    def test_noncritical_symlink_is_not_traversed_or_authenticated(self) -> None:
        (self.fx.root / "outside").symlink_to(self.base, target_is_directory=True)
        self.fx.verify()

    def test_observed_identity_mismatch_refuses(self) -> None:
        for change in (
            {"observed_sysroot": str(self.base)},
            {"observed_compiler": str(self.base / "trustc")},
            {"verbose": {"commit-hash": "b" * 40, "host": HOST}},
            {"verbose": {"commit-hash": REV, "host": "other-host"}},
        ):
            with self.subTest(change=change), self.assertRaises(ds.SealRefusal):
                self.fx.verify(**change)

    def test_artifact_byte_tampering_and_size_changes_refuse(self) -> None:
        for role in ("trustc", "targo", "driver"):
            path = self.fx.root / ("bin/" + role if role != "driver" else self.fx.table["driver_path"])
            original = path.read_bytes()
            for raw in (bytes([original[0] ^ 1]) + original[1:], original + b"extra"):
                with self.subTest(role=role, size=len(raw)):
                    path.write_bytes(raw)
                    try:
                        with self.assertRaises(ds.SealRefusal):
                            self.fx.verify()
                    finally:
                        path.write_bytes(original)

    def test_provenance_digest_mismatch_refuses(self) -> None:
        with (self.fx.root / "PROVENANCE").open("ab") as output:
            output.write(b"# changed\n")
        with self.assertRaisesRegex(ds.SealRefusal, "SHA256"):
            self.fx.verify()

    def test_duplicate_or_invalid_provenance_refuses_even_when_hash_is_updated(self) -> None:
        for extra in (b"reported_commit=" + REV.encode() + b"\n", b"invalid-line\n", b"extra=\xff\n"):
            with self.subTest(extra=extra):
                self.fx.write_provenance(extra)
                with self.assertRaises(ds.SealRefusal):
                    self.fx.verify()

    def test_mixed_incomplete_or_failed_build_stamp_refuses(self) -> None:
        changes = {
            "reported_commit": "b" * 40, "seal_name": "other-seal",
            "artifact_driver_name": "librustc_driver-other.so",
            "artifact_driver_sha256": "0" * 64, "artifact_driver_bytes": "1",
            "artifact_bin_trustc_sha256": "0" * 64, "artifact_bin_targo_sha256": "0" * 64,
            "build_stamp:head": "b" * 40, "build_stamp:record_version": "2",
            "build_stamp:tree_state": "dirty", "build_stamp:dirty_untracked": "1",
            "build_stamp:exit_status": "failed", "build_stamp:tree_changed_during_build": "yes",
            "build_stamp:end_tree_fingerprint": "e" * 64, "build_stamp:status_sha256": "e" * 64,
            "build_stamp:submodule_sha256": "e" * 64,
            "build_stamp:started_at": "-1", "build_stamp:completed_at": "1699999999",
        }
        for key, value in changes.items():
            with self.subTest(key=key):
                original = self.fx.fields[key]
                self.fx.fields[key] = value
                self.fx.write_provenance()
                try:
                    with self.assertRaises(ds.SealRefusal):
                        self.fx.verify()
                finally:
                    self.fx.fields[key] = original
        del self.fx.fields["build_stamp:head"]
        self.fx.write_provenance()
        with self.assertRaises(ds.SealRefusal):
            self.fx.verify()

    def test_incomplete_or_forged_fingerprint_and_completion_refuse(self) -> None:
        for key in ("build_stamp:submodule_sha256", "build_stamp:started_at", "build_stamp:completed_at"):
            original = self.fx.fields.pop(key)
            self.fx.write_provenance()
            try:
                with self.subTest(missing=key), self.assertRaises(ds.SealRefusal):
                    self.fx.verify()
            finally:
                self.fx.fields[key] = original
        for value in ("x", "-1", "0" * 20, "9" * 20):
            self.fx.fields["build_stamp:completed_at"] = value
            self.fx.write_provenance()
            with self.subTest(completion=value), self.assertRaises(ds.SealRefusal):
                self.fx.verify()
        self.fx.fields["build_stamp:completed_at"] = "1700000010"
        self.fx.fields["build_stamp:tree_fingerprint"] = "f" * 64
        self.fx.fields["build_stamp:end_tree_fingerprint"] = "f" * 64
        self.fx.write_provenance()
        with self.assertRaisesRegex(ds.SealRefusal, "recorded source facts"):
            self.fx.verify()

    def test_provenance_and_census_bounds_are_enforced(self) -> None:
        self.fx.write_provenance(b"#" * (ds.MAX_PROVENANCE_BYTES + 1))
        with self.assertRaisesRegex(ds.SealRefusal, "bounded size"):
            self.fx.verify()
        self.fx.write_provenance()
        for limit in ("MAX_CENSUS_ENTRIES", "MAX_CENSUS_DIRECTORIES", "MAX_CENSUS_DEPTH"):
            with self.subTest(limit=limit), mock.patch.object(ds, limit, 0):
                with self.assertRaises(ds.SealRefusal):
                    self.fx.verify()

    def test_path_replacement_during_stream_refuses(self) -> None:
        original = ds._Owner.read
        changed = False

        def replace(owner: ds._Owner, *args: object, **kwargs: object) -> bytes:
            nonlocal changed
            result = original(owner, *args, **kwargs)
            if not changed and not kwargs["retain"]:
                path = self.fx.root / "bin/trustc"
                raw = path.read_bytes()
                path.rename(self.base / "replaced")
                path.write_bytes(raw)
                path.chmod(0o755)
                changed = True
            return result

        with mock.patch.object(ds._Owner, "read", replace):
            with self.assertRaises(ds.SealRefusal):
                self.fx.verify()

    def during_admission(self, change: Callable[[], object]) -> mock._patch:
        """Run `change` after every input is held and before the final re-check."""
        original = ds._Owner.validate

        def validate(owner: ds._Owner) -> None:
            change()
            original(owner)

        return mock.patch.object(ds._Owner, "validate", validate)

    def test_unrelated_entries_in_an_ancestor_do_not_refuse(self) -> None:
        # An ancestor above the root (here the shared temporary directory's
        # child) gains and loses unrelated entries while a seal is admitted:
        # concurrent processes do this to a shared TMPDIR or a home directory.
        # Its times and link count move; no path to the root changes.
        def churn() -> None:
            (self.base / "neighbour").mkdir()
            (self.base / "neighbour-file").write_bytes(b"x")
            (self.base / "neighbour-file").unlink()

        with self.during_admission(churn):
            result = self.fx.verify()
        self.assertEqual(result["classification"], "development")

    def test_replaced_ancestor_refuses(self) -> None:
        fx = SealFixture(self.base / "ancestor" / "development")

        def replace() -> None:
            (self.base / "ancestor").rename(self.base / "moved")
            shutil.copytree(self.base / "moved", self.base / "ancestor", symlinks=True)

        with self.during_admission(replace):
            with self.assertRaisesRegex(ds.SealRefusal, "path binding changed"):
                fx.verify()

    def test_entries_added_inside_the_root_refuse(self) -> None:
        # Inside the root every held directory keeps its whole identity.
        with self.during_admission(lambda: (self.fx.root / "bin" / "added").write_bytes(b"x")):
            with self.assertRaisesRegex(ds.SealRefusal, "changed during admission"):
                self.fx.verify()

    def test_original_deadline_includes_cleanup_and_never_restarts(self) -> None:
        now = [0.0]
        original = ds._Owner.close

        def late_close(owner: ds._Owner) -> None:
            original(owner)
            now[0] = 1.0

        with mock.patch.object(ds._Owner, "close", late_close):
            with self.assertRaisesRegex(ds.SealRefusal, "deadline expired"):
                self.fx.verify(clock=lambda: now[0], timeout=1.0)
        for timeout in (0, -1, float("nan"), ds.READ_TIMEOUT_SECONDS + 1):
            with self.subTest(timeout=timeout), self.assertRaises(ds.SealRefusal):
                self.fx.verify(timeout=timeout)

    def test_schema_bounds_and_unknown_fields_refuse(self) -> None:
        for key, value in (
            ("root", "relative"), ("root", str(self.fx.root) + "/../other"),
            ("root", str(self.fx.root) + "/"), ("root", "//tmp/root"),
            ("host", ""), ("driver_path", "../driver.so"),
            ("driver_path", "lib/other.so"), ("trustc_sha256", "F" * 64),
            ("trustc_bytes", True), ("targo_bytes", 0),
            ("driver_bytes", ds.MAX_ARTIFACT_BYTES + 1), ("extra", "ignored"),
        ):
            table = dict(self.fx.table, **{key: value})
            with self.subTest(key=key, value=value), self.assertRaises(ds.SealRefusal):
                ds.DevelopmentSeal.parse(table)
        table = dict(self.fx.table, trustc_bytes=ds.MAX_ARTIFACT_BYTES, driver_bytes=ds.MAX_ARTIFACT_BYTES)
        with self.assertRaises(ds.SealRefusal):
            ds.DevelopmentSeal.parse(table)


if __name__ == "__main__":
    unittest.main()
