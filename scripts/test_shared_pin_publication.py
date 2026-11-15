#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Selected-source publication boundaries, independent of later-source drift."""
from copy import deepcopy
from pathlib import Path
import json
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import check_shared_pin_graph as graph
import test_check_live_main as fixtures
import check_live_main

SCRIPTS = Path(__file__).resolve().parent


class PublicationTests(unittest.TestCase):
    _git = fixtures.LiveMainTests._git
    _history = fixtures.LiveMainTests._history
    _agh_fixture = fixtures.LiveMainTests._agh_fixture
    _local_only_git = fixtures.LiveMainTests._local_only_git
    # Reuse real Git fixtures and transport assertions, not their test methods.
    def test_selected_source_accepts_changed_production_on_newer_main(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, first, second = self._history(root)
            self.assertNotEqual(self._git(checkout, 'show', first + ':src/lib.rs'),
                                self._git(root / 'seed', 'show', second + ':src/lib.rs'))
            self._git(checkout, 'remote', 'set-url', 'origin', 'https://github.com/alabsystems/ay.git')
            agh, _ = self._agh_fixture(root, checkout, [first, second])
            with patch.object(check_live_main, '_run_git', side_effect=self._local_only_git), \
                 patch.object(check_live_main, '_run_agh', side_effect=agh):
                self.assertEqual(check_live_main.require_frozen_main_ancestor(checkout, 'origin', first), second)
            self.assertEqual(self._git(checkout, 'rev-parse', 'HEAD'), first)

    def test_selected_source_rejects_ambiguous_main_advertisement_before_fetch(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout, first, second = self._history(Path(directory))
            self._git(checkout, 'remote', 'set-url', 'origin', 'https://github.com/alabsystems/ay.git')
            response = json.dumps([
                {"oid": first, "ref": "refs/heads/main"},
                {"oid": second, "ref": "refs/heads/main"},
            ])
            with patch.object(check_live_main, '_run_git', side_effect=self._local_only_git), \
                 patch.object(check_live_main, '_run_agh', return_value=fixtures.completed([], stdout=response)) as agh:
                with self.assertRaisesRegex(check_live_main.LiveMainError, 'malformed agh response'):
                    check_live_main.require_frozen_main_ancestor(checkout, 'origin', first)
            agh.assert_called_once_with(checkout, fixtures.AGH_MAIN)
            self.assertEqual(self._git(checkout, 'rev-parse', 'origin/main'), first)
            self.assertEqual(self._git(checkout, 'rev-parse', 'HEAD'), first)
            self.assertEqual(self._git(checkout, 'for-each-ref', 'refs/agh/'), '')

    def selected_checkout(self, checkout, revision):
        source = (SCRIPTS / 'check-shared-pins.sh').read_text()
        functions = source[source.index('die() {'):source.index('trust_ir_audit=')]
        return subprocess.run(['bash', '-c', functions + '\nrequire_clean_checkout fixture "$1" "$2"',
                               'test', str(checkout), revision], capture_output=True, text=True)

    def test_selected_physical_source_dirty_or_wrong_revision_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout, first, second = self._history(Path(directory))
            self.assertEqual(self.selected_checkout(checkout, first).returncode, 0)
            (checkout / 'src/lib.rs').write_text('pub fn drifted() {}\n')
            dirty = self.selected_checkout(checkout, first)
            self.assertEqual(dirty.returncode, 1)
            self.assertIn('dirty', dirty.stderr)
            self._git(checkout, 'restore', 'src/lib.rs')
            self._git(checkout, 'fetch', str(Path(directory) / 'remote.git'), second)
            self._git(checkout, 'checkout', '--detach', second)
            wrong = self.selected_checkout(checkout, first)
            self.assertEqual(wrong.returncode, 1)
            self.assertIn('differs from manifest', wrong.stderr)

    def test_wrong_family_canonical_remote_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout, _, _ = self._history(Path(directory))
            self._git(checkout, 'remote', 'set-url', 'origin', 'https://github.com/another-owner/trust-ir.git')
            source = (SCRIPTS / 'check-shared-pins.sh').read_text()
            functions = source[source.index('die() {'):source.index('trust_ir_audit=')]
            result = subprocess.run(['bash', '-c', functions + '\ncanonical_remote "$1" trust-ir',
                                     'test', str(checkout)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)

    def test_default_gate_never_runs_later_source_equivalence(self):
        source = (SCRIPTS / 'check-shared-pins.sh').read_text()
        self.assertNotIn('pinned_package_paths.py', source)
        self.assertNotIn('PIN_EXCLUSIONS=', source)
        self.assertIn('check_shared_pin_graph.py', source)
        diagnostic = (SCRIPTS / 'check-shared-pin-drift.sh').read_text()
        self.assertIn('pinned_package_paths.py" drift', diagnostic)
        self.assertIn('pin-exclusions.toml', diagnostic)


class GraphTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name) / 'trust-mc'
        (self.root / 'tools').mkdir(parents=True)
        self.ir, self.vc, self.clean = 'a'*40, 'b'*40, 'c'*40
        (self.root / 'tools/tuple.toml').write_text(
            f'[trust_ir]\nrev="{self.ir}"\n[trust_vc]\nrev="{self.vc}"\n[clean]\nrev="{self.clean}"\n')
        packages = [{'name':name, 'id':name, 'source':None,
                     'manifest_path':str(self.root.parent / 'trust-ir/crates' / name / 'Cargo.toml')}
                    for name in ('trust-ir','trust-ir-build')]
        packages += [{'name':name,'id':name,'source':f'git+https://github.com/alabsystems/{family}.git?rev={rev}#{rev}'}
                     for name,family,rev in (('trust-vc-merge-contract','trust-vc',self.vc),('clean-kernel','clean',self.clean))]
        self.metadata = {'packages':packages, 'resolve':{'nodes':[{'id':p['id'],'dependencies':
                        ['trust-ir','clean-kernel'] if p['name']=='trust-ir-build' else []} for p in packages]}}

    def validate(self, metadata):
        graph.validate(metadata, self.root, self.ir, self.vc, self.clean)

    def test_selected_graph_and_tuple_agree(self):
        self.validate(self.metadata)

    def test_wrong_transitive_source_or_fragment_and_duplicate_are_refused(self):
        for mutate in ('revision','fragment','duplicate','path','disconnected','tuple'):
            with self.subTest(mutate=mutate):
                metadata = deepcopy(self.metadata)
                kernel = metadata['packages'][-1]
                if mutate=='revision': kernel['source']=kernel['source'].replace(self.clean,'d'*40)
                elif mutate=='fragment': kernel['source']=kernel['source'].split('#')[0]+'#'+'d'*40
                elif mutate=='duplicate': metadata['packages'].append(deepcopy(kernel))
                elif mutate=='path': kernel['source']=None
                elif mutate=='disconnected': metadata['resolve']['nodes'][1]['dependencies']=['trust-ir']
                elif mutate=='tuple': (self.root/'tools/tuple.toml').write_text('[clean]\nrev="wrong"\n')
                with self.assertRaises(ValueError): self.validate(metadata)


if __name__ == '__main__':
    unittest.main()
