#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Versioned recorded-source admission; no toolchain or source-census execution."""

from __future__ import annotations

import hashlib
import io
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import development_seal as ds
import tuple_check as tc
from test_development_seal import HOST, REV, SealFixture


def fingerprint(fields: dict[str, str]) -> str:
    # Official v2 domain and ordering, independent of the reader's dispatch.
    names = (
        "head", "diff_sha256", "status_sha256", "submodule_sha256",
        "submodule_census_scope", "recursive_submodule_sha256", "recursive_submodule_count",
        "tree_state", "dirty_tracked", "dirty_untracked",
    )
    material = "trust-build-tree-provenance-v2\n" + "".join(
        fields["build_stamp:" + name] + "\n" for name in names
    )
    return hashlib.sha256(material.encode("utf-8")).hexdigest()


def version_two(fixture: SealFixture) -> None:
    fixture.fields.update({
        "source_census_scope": "recursive-worktrees/v1",
        "build_stamp:record_version": "2",
        "build_stamp:submodule_census_scope": "recursive-worktrees/v1",
        "build_stamp:recursive_submodule_sha256": hashlib.sha256(b"synthetic recursive census\n").hexdigest(),
        "build_stamp:recursive_submodule_count": "12",
    })
    value = fingerprint(fixture.fields)
    fixture.fields["build_stamp:tree_fingerprint"] = value
    fixture.fields["build_stamp:end_tree_fingerprint"] = value
    fixture.write_provenance()


class DevelopmentSealV2Tests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name).resolve()
        self.fx = SealFixture(self.base / "development")
        version_two(self.fx)

    def test_completed_v2_reports_only_recorded_recursive_authority(self) -> None:
        self.fx.write_provenance(b"build_stamp:# original copied completion comment\n")
        result = self.fx.verify()
        self.assertEqual(result["classification"], "development")
        self.assertEqual(result["build_stamp_version"], "2")
        self.assertEqual(result["recorded_source_census_scope"], "recursive-worktrees/v1")
        self.assertEqual(result["recorded_recursive_submodule_count"], 12)
        self.assertEqual(result["recorded_recursive_submodule_sha256"], self.fx.fields["build_stamp:recursive_submodule_sha256"])
        self.assertIn("source census not replayed", result["scope"])
        self.assertIn("no complete sysroot authentication", result["scope"])
        self.assertEqual([item["path"] for item in result["artifacts"]], ["bin/trustc", "bin/targo", self.fx.table["driver_path"]])

    def test_missing_recursive_or_original_completion_field_refuses(self) -> None:
        for key in (
            "source_census_scope", "build_stamp:submodule_census_scope",
            "build_stamp:recursive_submodule_sha256", "build_stamp:recursive_submodule_count",
            "build_stamp:head", "build_stamp:exit_status", "build_stamp:completed_at",
            "build_stamp:end_tree_fingerprint",
        ):
            original = self.fx.fields.pop(key)
            try:
                self.fx.write_provenance()
                with self.subTest(missing=key), self.assertRaises(ds.SealRefusal):
                    self.fx.verify()
            finally:
                self.fx.fields[key] = original

    def test_mixed_unsupported_or_disagreeing_scopes_refuse(self) -> None:
        original = dict(self.fx.fields)
        for key, values in (
            ("source_census_scope", ("top-level-only/v1", "recursive-worktrees/v2", "unavailable")),
            ("build_stamp:submodule_census_scope", ("top-level-only/v1", "recursive-worktrees/v2")),
            ("build_stamp:record_version", ("0", "3", "02", "1")),
        ):
            for value in values:
                self.fx.fields = dict(original, **{key: value})
                self.fx.write_provenance()
                with self.subTest(key=key, value=value), self.assertRaises(ds.SealRefusal):
                    self.fx.verify()

    def test_recursive_count_and_digest_remain_bounded_and_canonical(self) -> None:
        original = dict(self.fx.fields)
        for key, values in (
            ("build_stamp:recursive_submodule_count", ("-1", "01", "1.0", "true", "9" * 20)),
            ("build_stamp:recursive_submodule_sha256", ("x", "F" * 64, "e" * 63, "e" * 65)),
        ):
            for value in values:
                self.fx.fields = dict(original, **{key: value})
                self.fx.fields["build_stamp:tree_fingerprint"] = fingerprint(self.fx.fields)
                self.fx.fields["build_stamp:end_tree_fingerprint"] = self.fx.fields["build_stamp:tree_fingerprint"]
                self.fx.write_provenance()
                with self.subTest(key=key, value=value), self.assertRaises(ds.SealRefusal):
                    self.fx.verify()

    def test_zero_and_largest_official_count_are_recorded_without_allocating_a_census(self) -> None:
        for value in ("0", "9" * 19):
            self.fx.fields["build_stamp:recursive_submodule_count"] = value
            digest = fingerprint(self.fx.fields)
            self.fx.fields["build_stamp:tree_fingerprint"] = digest
            self.fx.fields["build_stamp:end_tree_fingerprint"] = digest
            self.fx.write_provenance()
            with self.subTest(count=value):
                result = self.fx.verify()
                self.assertEqual(result["recorded_recursive_submodule_count"], int(value))
                self.assertIn("source census not replayed", result["scope"])

    def test_recorded_recursive_facts_and_domain_are_bound(self) -> None:
        original = dict(self.fx.fields)
        for key, value in (
            ("build_stamp:recursive_submodule_count", "13"),
            ("build_stamp:recursive_submodule_sha256", "e" * 64),
            ("build_stamp:submodule_sha256", "e" * 64),
        ):
            self.fx.fields = dict(original, **{key: value})
            self.fx.write_provenance()
            with self.subTest(key=key), self.assertRaisesRegex(ds.SealRefusal, "recorded source facts"):
                self.fx.verify()
        self.fx.fields = dict(original)
        legacy = "".join(original["build_stamp:" + key] + "\n" for key in (
            "head", "diff_sha256", "status_sha256", "submodule_sha256",
        ))
        for material in (legacy, "".join(original["build_stamp:" + key] + "\n" for key in ds.STAMP_BASE_IDENTITY + ds.STAMP_RECURSIVE_IDENTITY)):
            value = hashlib.sha256(material.encode()).hexdigest()
            self.fx.fields["build_stamp:tree_fingerprint"] = value
            self.fx.fields["build_stamp:end_tree_fingerprint"] = value
            self.fx.write_provenance()
            with self.subTest(material=material), self.assertRaisesRegex(ds.SealRefusal, "recorded source facts"):
                self.fx.verify()

    def test_wrong_source_dirty_failed_changed_and_late_completion_refuse(self) -> None:
        original = dict(self.fx.fields)
        for key, value in (
            ("reported_commit", "b" * 40), ("build_stamp:head", "b" * 40),
            ("sealtime_repo_head", "b" * 40), ("build_stamp:tree_state", "dirty"),
            ("build_stamp:dirty_tracked", "1"), ("build_stamp:dirty_untracked", "1"),
            ("build_stamp:exit_status", "failed"), ("build_stamp:tree_changed_during_build", "YES"),
            ("build_stamp:end_tree_fingerprint", "e" * 64),
            ("build_stamp:completed_at", "1699999999"),
        ):
            self.fx.fields = dict(original, **{key: value})
            self.fx.write_provenance()
            with self.subTest(key=key), self.assertRaises(ds.SealRefusal):
                self.fx.verify()

    def test_v1_keeps_exact_scope_and_cannot_acquire_recursive_fields(self) -> None:
        legacy = SealFixture(self.base / "legacy")
        result = legacy.verify()
        self.assertEqual(result["scope"], ds.IDENTITY_SCOPE)
        self.assertEqual(result["build_stamp_scope"], "top-level source state only")
        self.assertNotIn("recorded_recursive_submodule_count", result)
        legacy.fields["source_census_scope"] = "top-level-only/v1"
        legacy.write_provenance()
        self.assertEqual(legacy.verify()["scope"], ds.IDENTITY_SCOPE)
        original = dict(legacy.fields)
        for key, value in (
            ("source_census_scope", "recursive-worktrees/v1"),
            ("source_census_scope", "recursive-worktrees/v2"),
            ("build_stamp:submodule_census_scope", "recursive-worktrees/v1"),
            ("build_stamp:recursive_submodule_sha256", "e" * 64),
            ("build_stamp:recursive_submodule_count", "12"),
        ):
            legacy.fields = dict(original, **{key: value})
            legacy.write_provenance()
            with self.subTest(key=key), self.assertRaises(ds.SealRefusal):
                legacy.verify()

    def test_v2_tampered_provenance_artifact_and_external_alias_refuse(self) -> None:
        with (self.fx.root / "PROVENANCE").open("ab") as output:
            output.write(b"# tampered after hash\n")
        with self.assertRaises(ds.SealRefusal):
            self.fx.verify()
        self.fx.write_provenance()
        path = self.fx.root / "bin/targo"
        raw = path.read_bytes()
        path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
        with self.assertRaises(ds.SealRefusal):
            self.fx.verify()
        path.write_bytes(raw)
        os.link(path, self.base / "external-targo")
        with self.assertRaisesRegex(ds.SealRefusal, "external hardlinks"):
            self.fx.verify()

    def test_v2_original_deadline_includes_final_descriptor_cleanup(self) -> None:
        now = [0.0]
        original = ds._Owner.close

        def close(owner: ds._Owner) -> None:
            original(owner)
            now[0] = 1.0

        with mock.patch.object(ds._Owner, "close", close):
            with self.assertRaisesRegex(ds.SealRefusal, "original deadline expired"):
                self.fx.verify(clock=lambda: now[0], timeout=1.0)

    def test_schema_two_report_and_text_use_authenticated_v2_scope(self) -> None:
        source = Path(__file__).resolve().parent.parent / "tools/tuple.toml"
        document = dict(tc.load_tuple(source).document)
        document.update(schema=2, trust={"rev": REV, "channel": "trust", "identity": "development"})
        document["development_seal"] = self.fx.table
        tuple_path = self.base / "development.toml"
        lines = ["schema = 2"]
        for name, fields in document.items():
            if name != "schema":
                lines += [f"[{name}]"] + [f"{key} = {json.dumps(value)}" for key, value in fields.items()]
        tuple_path.write_text("\n".join(lines) + "\n")
        probe = tc.ToolchainProbe(
            rustc=str(self.fx.root / "bin/trustc"), sysroot=str(self.fx.root),
            verbose={"commit-hash": REV, "host": HOST},
        )

        def only_identity(_layout: tc.Layout, selected: tc.MeasurementTuple) -> tuple:
            return [tc.check_trust_commit(probe, selected), tc.check_trust_build(probe, selected)], probe

        with mock.patch.object(tc, "run_checks", only_identity), mock.patch.object(tc, "_trust_mc_state", return_value={}):
            report = tc.evaluate(self.base, tuple_path)
        self.assertTrue(report["trust"]["development_identity_established"])
        self.assertEqual(report["trust"]["identity_scope"], ds.RECURSIVE_IDENTITY_SCOPE)
        self.assertIn(ds.RECURSIVE_IDENTITY_SCOPE, report["checks"][1]["message"])
        with mock.patch("sys.stdout", new_callable=io.StringIO) as output:
            tc._print_text(report)
        self.assertIn(ds.RECURSIVE_IDENTITY_SCOPE, output.getvalue())
        # The committed tuple names a numbered seal at another commit, never this
        # development build. Read it rather than copy its values here: copies
        # went stale on every tuple bump (9192, then 15698).
        committed = tc.load_tuple(source)
        self.assertIs(type(committed.trust_build), int)
        self.assertGreater(committed.trust_build, 0)
        self.assertNotEqual(committed.trust_rev, REV)
        self.assertEqual(tc.check_trust_commit(probe, committed).status, tc.FAIL)
        self.assertEqual(tc.check_trust_build(probe, committed).status, tc.FAIL)
        (self.fx.root / "bin/targo").write_bytes(b"tampered")
        with mock.patch.object(tc, "run_checks", only_identity), mock.patch.object(tc, "_trust_mc_state", return_value={}):
            refused = tc.evaluate(self.base, tuple_path)
        self.assertFalse(refused["trust"]["development_identity_established"])
        self.assertIsNone(refused["trust"]["development_identity"])


if __name__ == "__main__":
    unittest.main()
