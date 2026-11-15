#!/usr/bin/env python3
"""Exercise real ancestry under hostile ambient and cached Git state."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import check_live_main
from git_authority_environment import git_environment, git_transport_environment

class GitAuthorityEnvironment(unittest.TestCase):
    def test_fetch_can_use_configured_helper_without_gaining_history_authority(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / '.gitconfig').write_text('''[credential]
    helper =
    helper = "!f() { echo username=fixture-user; echo password=fixture-only; }; f"
''')
            with patch.dict(os.environ, {'HOME': str(root),
                                         'XDG_CONFIG_HOME': str(root / 'xdg'),
                                         'PATH': os.environ['PATH']}, clear=True):
                transport = git_transport_environment(root)
                authority = git_environment()
            query = 'protocol=https\nhost=fixture.invalid\n\n'
            fetched = subprocess.run(['git', 'credential', 'fill'], cwd=root,
                                     env=transport, input=query, text=True,
                                     capture_output=True, timeout=10)
            self.assertEqual(fetched.returncode, 0, fetched.stderr)
            self.assertIn('password=fixture-only', fetched.stdout)
            refused = subprocess.run(['git', 'credential', 'fill'], cwd=root,
                                     env=authority, input=query, text=True,
                                     capture_output=True, timeout=10)
            self.assertNotEqual(refused.returncode, 0)

    def test_fetch_copies_only_credential_settings_from_normal_config(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config = root / '.gitconfig'
            config.write_text('''[credential]
    helper =
    helper = !printf fixture
[credential "https://github.com"]
    username = fixture-user
    useHttpPath = true
[url "https://unrelated.invalid/"]
    insteadOf = https://github.com/
[core]
    hooksPath = /unrelated/hooks
''')
            environment = {'HOME': str(root), 'XDG_CONFIG_HOME': str(root / 'xdg'),
                           'PATH': os.environ['PATH'], 'GIT_CONFIG_COUNT': '1',
                           'GIT_CONFIG_KEY_0': 'credential.helper',
                           'GIT_CONFIG_VALUE_0': '!printf hostile',
                           'GIT_OBJECT_DIRECTORY': '/hostile/objects'}
            with patch.dict(os.environ, environment, clear=True):
                actual = git_transport_environment(root)
            result = subprocess.run(['git', 'config', '--null', '--list'],
                                    cwd=root, env=actual, capture_output=True, check=True)
            rows = result.stdout.split(b'\0')[:-1]
            self.assertEqual(rows[-4:], [
                b'credential.helper\n', b'credential.helper\n!printf fixture',
                b'credential.https://github.com.username\nfixture-user',
                b'credential.https://github.com.usehttppath\ntrue',
            ])
            self.assertTrue(all(row.startswith(b'credential.') for row in rows))
            self.assertEqual(actual['GIT_CONFIG_GLOBAL'], os.devnull)
            self.assertEqual(actual['GIT_NO_REPLACE_OBJECTS'], '1')
            self.assertEqual(actual['GIT_GRAFT_FILE'], os.devnull)
            self.assertNotIn('GIT_OBJECT_DIRECTORY', actual)

    def test_environment_excludes_ambient_authority(self):
        hostile = {name: 'hostile' for name in (
            'GIT_DIR', 'GIT_WORK_TREE', 'GIT_COMMON_DIR', 'GIT_OBJECT_DIRECTORY',
            'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_CONFIG_COUNT', 'GIT_CONFIG_PARAMETERS',
            'GIT_NAMESPACE', 'GIT_SHALLOW_FILE', 'GIT_TEMPLATE_DIR',
            'GIT_DEFAULT_HASH', 'GIT_DEFAULT_REF_FORMAT', 'GIT_GRAFT_FILE')}
        with patch.dict(os.environ, dict(hostile, CARGO_BUILD_JOBS='6'), clear=True):
            actual = git_environment()
        self.assertEqual(actual['GIT_CONFIG_GLOBAL'], os.devnull)
        self.assertEqual(actual['GIT_CONFIG_NOSYSTEM'], '1')
        self.assertEqual(actual['GIT_GRAFT_FILE'], os.devnull)
        self.assertEqual(actual['GIT_NO_REPLACE_OBJECTS'], '1')
        self.assertEqual(actual['GIT_NO_LAZY_FETCH'], '1')
        self.assertEqual(actual['CARGO_BUILD_JOBS'], '6')
        for key in hostile.keys() - {'GIT_GRAFT_FILE'}:
            self.assertNotIn(key, actual)

    def test_unrelated_root_is_not_admitted_by_grafts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            repo = root / 'repo'
            subprocess.run(['git', 'init', '--template=', '--object-format=sha1', str(repo)], check=True, capture_output=True)
            def raw(*args, env=None):
                return subprocess.run(['git', '-C', str(repo), *args], input=None, text=True, capture_output=True, env=env)
            tree = raw('mktree').stdout.strip()
            env = dict(os.environ, GIT_AUTHOR_NAME='Fixture', GIT_AUTHOR_EMAIL='fixture@example.invalid', GIT_COMMITTER_NAME='Fixture', GIT_COMMITTER_EMAIL='fixture@example.invalid')
            a = raw('commit-tree', tree, '-m', 'one', env=env).stdout.strip()
            b = raw('commit-tree', tree, '-m', 'two', env=env).stdout.strip()
            self.assertEqual(raw('merge-base', '--is-ancestor', a, b).returncode, 1)
            for cached in (False, True):
                graft = repo / '.git/info/grafts' if cached else root / 'grafts'
                graft.parent.mkdir(exist_ok=True)
                graft.write_text(f'{b} {a}\n')
                hostile = dict(os.environ, GIT_NO_REPLACE_OBJECTS='1')
                if not cached:
                    hostile['GIT_GRAFT_FILE'] = str(graft)
                with self.subTest(cached=cached), patch.dict(os.environ, hostile, clear=True):
                    self.assertEqual(raw('merge-base', '--is-ancestor', a, b).returncode, 0)
                    self.assertEqual(check_live_main._run_git(repo, ('merge-base', '--is-ancestor', a, b)).returncode, 1)
                    self.assertEqual(check_live_main._run_git(repo, ('merge-base', '--is-ancestor', a, a)).returncode, 0)
                graft.unlink()

if __name__ == '__main__':
    unittest.main()
