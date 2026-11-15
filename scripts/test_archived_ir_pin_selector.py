#!/usr/bin/env python3
"""Consumer regressions for IR-owned sealed historical selector data."""
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

MC=Path(__file__).resolve().parents[1]
IR=MC.parent/'trust-ir'
sys.path.insert(0,str(MC/'scripts'))
from check_first_party_git_pins import audit_repository, _archived_ir_manifest
PACKET='reports/2026-11-08-source-value-operational/evidence/afa-corrected-compact'
ENDPOINT=PACKET+'/source/crates/trust-ir-build/Cargo.toml'
NEW='789c68a6ed9779d2d348f86ac7ec14429d75b7c2'
OLD='7f25ef5deae5f41637d9c24ed512aea6a07ac310'
class ArchivedSelectorConsumer(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='mc sealed IR ')
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.env=dict(os.environ,GIT_CONFIG_GLOBAL=os.devnull,GIT_CONFIG_NOSYSTEM='1',GIT_AUTHOR_NAME='Fixture',GIT_AUTHOR_EMAIL='fixture@example.invalid',GIT_COMMITTER_NAME='Fixture',GIT_COMMITTER_EMAIL='fixture@example.invalid')
        (self.root/'scripts').mkdir()
        shutil.copyfile(IR/'scripts/pin_rewrite.py',self.root/'scripts/pin_rewrite.py')
        # IR a3dcbedc keeps the sealed historical snapshot as source.tar.gz, outside
        # Cargo discovery; a historical IR tree still has source/, which this
        # fixture restores from the archive outside any IR checkout.
        (self.root/PACKET).mkdir(parents=True)
        with tarfile.open(IR/PACKET/'source.tar.gz') as archive: archive.extractall(self.root/PACKET,filter='data')
        shutil.copyfile(IR/PACKET/'artifact-manifest.json',self.root/PACKET/'artifact-manifest.json')
        text='[workspace]\nmembers=[]\n[workspace.dependencies]\n'
        text+=''.join(name+'={git="https://github.com/alabsystems/clean.git",rev="'+NEW+'"}\n' for name in ['clean-kernel','clean-mathverse','clean-olean'])
        (self.root/'Cargo.toml').write_text(text)
        self.git('init','-q');self.git('add','-A');self.git('commit','-qm','sealed historical source fixture')
    def git(self,*args):
        subprocess.run(['git','-C',str(self.root),*args],env=self.env,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    def test_maintained_owner_authenticates_only_exact_historical_endpoint(self):
        self.assertEqual(audit_repository(self.root,'clean').revision,NEW)
        neighbor=self.root/'reports/neighbor/Cargo.toml';neighbor.parent.mkdir(parents=True);neighbor.write_bytes((self.root/ENDPOINT).read_bytes())
        self.assertFalse(_archived_ir_manifest(self.root,neighbor))
        self.git('add','-A');self.git('commit','-qm','live neighboring selector')
        with self.assertRaises(ValueError): audit_repository(self.root,'clean')
    def test_altered_archive_never_hidden_by_updating_it_to_current_pin(self):
        endpoint=self.root/ENDPOINT;endpoint.write_text(endpoint.read_text().replace(OLD,NEW))
        with self.assertRaises(ValueError): audit_repository(self.root,'clean')
    def test_missing_seal_and_new_source_neighbor_refuse(self):
        seal=self.root/PACKET/'artifact-manifest.json';seal.unlink()
        with self.assertRaises(ValueError): audit_repository(self.root,'clean')
        shutil.copyfile(IR/PACKET/'artifact-manifest.json',seal)
        (self.root/PACKET/'source/new.rs').write_text('// unsealed')
        with self.assertRaises(ValueError): audit_repository(self.root,'clean')
    def test_live_path_adoption_is_not_historical_data(self):
        root=self.root/'Cargo.toml';root.write_text(root.read_text()+'archived={path="'+PACKET+'/source/crates/trust-ir-build"}\n')
        with self.assertRaises(ValueError): audit_repository(self.root,'clean')
    def test_dependency_cannot_modify_its_owner_to_authorize_an_exemption(self):
        helper=self.root/'scripts/pin_rewrite.py';helper.write_text('def validate_archived_pin_boundary(*args):pass\ndef is_archived_pin_input(*args):return True\n')
        self.git('add','scripts/pin_rewrite.py');self.git('commit','-qm','hostile owner substitution')
        with self.assertRaises(ValueError): audit_repository(self.root,'clean')
if __name__=='__main__':unittest.main()
