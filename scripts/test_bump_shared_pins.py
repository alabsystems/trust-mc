#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Exercise the pin transaction with real Git siblings and a fake frontend."""

import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest import mock

from python_executable import python_executable_header


SCRIPT = Path(__file__).with_name("bump-shared-pins.py")
sys.path.insert(0, str(SCRIPT.parent))
spec = importlib.util.spec_from_file_location("bump_shared_pins", SCRIPT)
bump = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bump)
CLEAN_OLD = "a" * 40
CLEAN_NEW = "b" * 40


def git(root, *arguments):
    return subprocess.check_output(
        ["git", "-c", "user.name=Pin fixture", "-c", "user.email=fixture@example.invalid",
         "-c", "core.hooksPath=/dev/null", "-C", str(root), *arguments],
        text=True, stderr=subprocess.PIPE,
    ).strip()


def commit(root):
    git(root, "add", ".")
    git(root, "commit", "-qm", "fixture")
    return git(root, "rev-parse", "HEAD")


class SharedPinTransaction(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="MC pin transaction ")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        cargo_home = mock.patch.dict(os.environ, {"CARGO_HOME": str(self.base / "cargo-home")})
        cargo_home.start()
        self.addCleanup(cargo_home.stop)
        self.root = self.base / "trust-mc"
        ir = self.base / "trust-ir"
        vc = self.base / "trust-vc"
        for root in (self.root, ir, vc):
            root.mkdir()
            git(root, "init", "-q")
        clean_deps = "\n".join(
            f'{name} = {{ git = "{bump.FAMILIES["clean"].url}", rev = "{CLEAN_OLD}" }}'
            for name in ("clean-kernel", "clean-mathverse", "clean-olean")
        )
        (ir / "Cargo.toml").write_text("[workspace.dependencies]\n" + clean_deps + "\n")
        for name in ("trust-ir", "trust-ir-build"):
            path = ir / "crates" / name
            path.mkdir(parents=True)
            (path / "Cargo.toml").write_text(f'[package]\nname="{name}"\nversion="0.1.0"\n')
        self.old_ir = commit(ir)
        (ir / "Cargo.toml").write_text((ir / "Cargo.toml").read_text().replace(CLEAN_OLD, CLEAN_NEW))
        self.new_ir = commit(ir)
        (vc / "Cargo.toml").write_text('[package]\nname="trust-vc-merge-contract"\nversion="0.1.0"\n')
        self.old_vc = commit(vc)
        (vc / "change").write_text("new revision\n")
        self.new_vc = commit(vc)
        ir_url, vc_url = bump.FAMILIES["trust-ir"].url, bump.FAMILIES["trust-vc"].url
        (self.root / "Cargo.toml").write_text(
            '[workspace]\nmembers=["driver", "replay", "ingest"]\n'
            f'[patch."{ir_url}"]\ntrust-ir={{path="../trust-ir/crates/trust-ir"}}\n'
            'trust-ir-build={path="../trust-ir/crates/trust-ir-build"}\n'
        )
        manifests = {
            "driver": f'''[dependencies]
ir = {{ package="trust-ir", git="{ir_url}", rev="{self.old_ir}", optional=true }}
[build-dependencies]
builder = {{ package="trust-ir-build", git="{ir_url}", rev="{self.old_ir}" }}
[target.'cfg(unix)'.dev-dependencies]
ir = {{ package="trust-ir", git="{ir_url}", rev="{self.old_ir}", features=["serde"] }}
''',
            "replay": f'''[dependencies.ir]
package="trust-ir"
git="{ir_url}"
rev='{self.old_ir}' # preserve this comment
''',
            "ingest": f'''[dependencies]
contract = {{ package="trust-vc-merge-contract", git="{vc_url}", rev="{self.old_vc}" }}
''',
        }
        for name, text in manifests.items():
            path = self.root / name / "Cargo.toml"
            path.parent.mkdir()
            path.write_text(f'[package]\nname="{name}"\nversion="0.1.0"\n' + text)
        (self.root / "driver/Cargo.toml").chmod(0o640)
        (self.root / "tools").mkdir()
        (self.root / "tools/tuple.toml").write_text(
            f'schema=1\n[trust]\nrev="{self.old_ir}"\nbuild=15698\n'
            f'[ay]\nrev="{self.old_ir}"\n[trust_ir]\nrev="{self.old_ir}" # IR\n'
            f'[trust_vc]\nrev="{self.old_vc}"\n[clean]\nrev="{CLEAN_OLD}"\n'
        )
        (self.root / "Cargo.lock").write_text(self.lock(self.old_vc, CLEAN_OLD))
        commit(self.root)
        self.before = {path: path.read_bytes() for path in self.root.rglob("Cargo.*")}
        self.before[self.root / "tools/tuple.toml"] = (self.root / "tools/tuple.toml").read_bytes()
        self.old_tuple = tomllib.loads(self.before[self.root / "tools/tuple.toml"].decode())
        metadata = {"packages": [
            {"name": name, "source": None, "manifest_path": str(ir / "crates" / name / "Cargo.toml")}
            for name in ("trust-ir", "trust-ir-build")
        ] + [
            {"name": name, "source": f"git+{bump.FAMILIES[family].url}?rev={revision}#{revision}"}
            for name, family, revision in (
                ("trust-vc-merge-contract", "trust-vc", self.new_vc),
                ("clean-kernel", "clean", CLEAN_NEW),
            )
        ]}
        (self.root / ".metadata.json").write_text(json.dumps(metadata))
        (self.root / ".new-lock").write_text(self.lock(self.new_vc, CLEAN_NEW))
        scripts = self.root / "scripts"
        scripts.mkdir()
        frontend = scripts / "targo"
        frontend.write_text(python_executable_header(sys.executable) + f'''import json, os, signal, subprocess, sys, time
from pathlib import Path
root = Path.cwd()
args = sys.argv[1:]
mode = (root / ".mode").read_text() if (root / ".mode").exists() else "ok"
if args == ["--unverified", "--version"]:
    if mode == "stock-frontend": raise SystemExit(99)
    print("targo fixture")
    raise SystemExit(0)
with (root / ".calls").open("a") as out: out.write(json.dumps(args)+"\\n")
if not args or args[0] != "metadata": raise SystemExit(91)
locked = "--locked" in args
if not locked:
    (root / "Cargo.lock").write_bytes((root / ".new-lock").read_bytes())
    if mode == "refresh-failure": raise SystemExit(31)
    if mode == "interrupt":
        (root / ".child-pid").write_text(str(os.getpid()))
        os.kill(os.getppid(), signal.SIGTERM)
        time.sleep(2)
        (root / "Cargo.lock").write_text("late write must not happen")
    if mode == "external-edit":
        with (root / "driver/Cargo.toml").open("a") as out: out.write("# external edit\\n")
    if mode == "sibling-edit":
        with (root.parent / "trust-ir/Cargo.toml").open("a") as out: out.write("# sibling edit\\n")
    if mode == "unrelated-lock":
        lock = root / "Cargo.lock"
        lock.write_text(lock.read_text().replace('checksum="stable"', 'checksum="tampered"'))
    if mode == "late-writer":
        child = subprocess.Popen([sys.executable, "-c",
            "import time; from pathlib import Path; time.sleep(0.3); Path('Cargo.lock').write_text('late write')"],
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        (root / ".late-pid").write_text(str(child.pid))
        print("bad json")
        raise SystemExit(0)
if locked and mode == "locked-failure":
    (root / ".validation-failed").touch()
    raise SystemExit(32)
metadata = json.loads((root / ".metadata.json").read_text())
if locked and mode == "wrong-clean": metadata["packages"][-1]["source"] = "wrong"
if locked and mode == "wrong-ir": metadata["packages"][0]["manifest_path"] = "/wrong/Cargo.toml"
if locked and mode == "duplicate-ir": metadata["packages"].append(metadata["packages"][0])
if locked and mode == "bad-json": print("not json")
else: print(json.dumps(metadata))
''')
        frontend.chmod(0o700)
        resolver = scripts / "resolve-trust-tool.sh"
        resolver.write_text(f'#!/bin/sh\nprintf "%s\\n" "{frontend}"\n')
        resolver.chmod(0o700)

    def lock(self, vc, clean):
        return f'''version = 4
[[package]]
name="driver"
version="0.1.0"
dependencies=["trust-ir", "trust-vc-merge-contract", "unrelated"]
[[package]]
name="trust-ir"
version="0.1.0"
dependencies=["clean-kernel"]
[[package]]
name="trust-ir-build"
version="0.1.0"
dependencies=["clean-kernel"]
[[package]]
name="trust-vc-merge-contract"
version="0.1.0"
source="git+{bump.FAMILIES['trust-vc'].url}?rev={vc}#{vc}"
[[package]]
name="clean-kernel"
version="0.9.0"
source="git+{bump.FAMILIES['clean'].url}?rev={clean}#{clean}"
[[package]]
name="unrelated"
version="1.0.0"
source="registry+https://example.invalid/index"
checksum="stable"
'''

    def mode(self, name):
        (self.root / ".mode").write_text(name)

    def assert_restored(self):
        for path, contents in self.before.items():
            self.assertEqual(path.read_bytes(), contents, str(path))
        self.assertEqual((self.root / "driver/Cargo.toml").stat().st_mode & 0o777, 0o640)

    def test_updates_alias_build_target_and_tuple_without_changing_other_authorities(self):
        self.assertTrue(bump.update(self.root, self.new_ir, self.new_vc))
        self.assertEqual(bump.audit_repository(self.root, "trust-ir").revision, self.new_ir)
        self.assertEqual(bump.audit_repository(self.root, "trust-vc").revision, self.new_vc)
        actual = tomllib.loads((self.root / "tools/tuple.toml").read_text())
        expected = self.old_tuple | {"trust_ir": {"rev": self.new_ir}, "trust_vc": {"rev": self.new_vc},
                                     "clean": {"rev": CLEAN_NEW}}
        self.assertEqual(actual, expected)
        self.assertEqual((self.root / "Cargo.toml").read_bytes(), self.before[self.root / "Cargo.toml"])
        self.assertIn("# preserve this comment", (self.root / "replay/Cargo.toml").read_text())
        self.assertEqual((self.root / "driver/Cargo.toml").stat().st_mode & 0o777, 0o640)
        calls = [json.loads(line) for line in (self.root / ".calls").read_text().splitlines()]
        self.assertNotIn("--locked", calls[0])
        self.assertIn("--locked", calls[1])

    def test_failures_restore_every_owned_input(self):
        for mode in ("refresh-failure", "locked-failure", "wrong-clean", "wrong-ir",
                     "duplicate-ir", "bad-json", "unrelated-lock"):
            with self.subTest(mode=mode):
                self.mode(mode)
                with self.assertRaises((ValueError, subprocess.CalledProcessError)):
                    bump.update(self.root, self.new_ir, self.new_vc)
                self.assert_restored()

    def test_noop_still_validates_the_lock_and_its_resolved_authorities(self):
        bump.update(self.root, self.new_ir, self.new_vc)
        self.assertFalse(bump.update(self.root, self.new_ir, self.new_vc))
        snapshot = (self.root / "Cargo.lock").read_bytes()
        self.mode("wrong-clean")
        with self.assertRaises(ValueError):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assertEqual((self.root / "Cargo.lock").read_bytes(), snapshot)

    def test_ambiguous_rewrite_and_stale_old_clean_refuse_before_frontend(self):
        path = self.root / "driver/Cargo.toml"
        path.write_text(path.read_text() + f'# rev="{self.old_ir}"\n')
        with self.assertRaisesRegex(ValueError, "identify only"):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assertFalse((self.root / ".calls").exists())
        path.write_bytes(self.before[path])
        path = self.root / "tools/tuple.toml"
        path.write_text(path.read_text().replace(CLEAN_OLD, "c" * 40))
        with self.assertRaisesRegex(ValueError, "old TrustIR"):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assertFalse((self.root / ".calls").exists())

    def test_clean_vc_descendant_remains_a_valid_frozen_checkout(self):
        vc = self.base / "trust-vc"
        (vc / "later").write_text("later\n")
        commit(vc)
        self.assertTrue(bump.update(self.root, self.new_ir, self.new_vc))

    def test_new_dependency_of_changed_clean_authority_is_allowed(self):
        path = self.root / ".new-lock"
        text = path.read_text().replace('name="clean-kernel"\n',
                                        'name="clean-kernel"\ndependencies=["new-transitive"]\n')
        text += '\n[[package]]\nname="new-transitive"\nversion="1.0.0"\n'
        path.write_text(text)
        self.assertTrue(bump.update(self.root, self.new_ir, self.new_vc))

    def test_new_unrelated_package_is_refused(self):
        path = self.root / ".new-lock"
        path.write_text(path.read_text() + '\n[[package]]\nname="unrelated-addition"\nversion="1.0.0"\n')
        with self.assertRaisesRegex(ValueError, "unrelated dependency"):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assert_restored()

    def test_outside_consumer_keeps_its_edge_to_a_shared_transitive_dependency(self):
        before = '''version=4
[[package]]
name="driver"
version="1.0.0"
dependencies=["trust-ir", "shared"]
[[package]]
name="trust-ir"
version="1.0.0"
dependencies=["shared"]
[[package]]
name="shared"
version="1.0.0"
'''
        after = before.replace('dependencies=["trust-ir", "shared"]', 'dependencies=["trust-ir"]')
        with self.assertRaisesRegex(ValueError, "unrelated dependency"):
            bump.validate_lock_change(before.encode(), after.encode())

    def test_write_failure_restores_prior_successful_writes(self):
        original = bump.write_atomic
        calls = 0
        def fail_once(path, data):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise OSError("fixture write failure")
            original(path, data)
        with mock.patch.object(bump, "write_atomic", side_effect=fail_once):
            with self.assertRaisesRegex(OSError, "fixture write failure"):
                bump.update(self.root, self.new_ir, self.new_vc)
        self.assert_restored()

    def test_sibling_change_invalidates_transaction_without_overwriting_it(self):
        self.mode("sibling-edit")
        with self.assertRaisesRegex(ValueError, "dirty"):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assert_restored()
        self.assertTrue((self.base / "trust-ir/Cargo.toml").read_text().endswith("# sibling edit\n"))

    def test_dirty_ir_refuses_without_mutating_the_consumer(self):
        (self.base / "trust-ir/Cargo.toml").write_text("# changed\n")
        with self.assertRaisesRegex(ValueError, "dirty"):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assert_restored()

    def test_stock_frontend_is_refused_before_any_mutation(self):
        self.mode("stock-frontend")
        with self.assertRaises(subprocess.CalledProcessError):
            bump.update(self.root, self.new_ir, self.new_vc)
        self.assert_restored()
        self.assertFalse((self.root / ".calls").exists())

    @unittest.skipUnless(os.name == "posix", "POSIX process ownership")
    def test_stop_during_launch_publishes_child_before_cleanup(self):
        original = bump.subprocess.Popen
        created = []
        def interrupted(*args, **kwargs):
            child = original(*args, **kwargs)
            if args and "metadata" in args[0]:
                created.append(child)
                os.kill(os.getpid(), signal.SIGTERM)
                os.kill(os.getpid(), signal.SIGINT)
            return child
        with mock.patch.object(bump.subprocess, "Popen", side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                bump.update(self.root, self.new_ir, self.new_vc)
        self.assert_restored()
        self.assertEqual(len(created), 1)
        self.assertIsNotNone(created[0].returncode)

    def test_old_authority_keeps_complete_original_source_and_git_identity(self):
        ir = self.base / "trust-ir"
        evidence = ir / "sealed-original.txt"
        evidence.write_text("original sealed source\n")
        revision = commit(ir)
        def audit(snapshot, family):
            self.assertEqual(family, "clean")
            self.assertEqual(git(snapshot, "rev-parse", "HEAD"), revision)
            self.assertEqual((snapshot / "sealed-original.txt").read_bytes(), evidence.read_bytes())
            self.assertEqual(git(snapshot, "status", "--porcelain"), "")
            return type("Audit", (), {"revision": CLEAN_OLD})()
        with mock.patch.object(bump, "audit_repository", side_effect=audit):
            self.assertEqual(bump.clean_pin_at_revision(ir, revision), CLEAN_OLD)
        self.assertEqual(git(ir, "rev-parse", "HEAD"), revision)

    def test_old_authority_materializes_source_hidden_by_parent_sparse_checkout(self):
        ir = self.base / "trust-ir"
        evidence = ir / "reports/historical-input.txt"
        evidence.parent.mkdir()
        expected = b"original sealed source\n"
        evidence.write_bytes(expected)
        revision = commit(ir)
        git(ir, "sparse-checkout", "set", "--no-cone", "/*", "!/reports/")
        self.assertFalse(evidence.exists())

        def audit(snapshot, family):
            self.assertEqual(family, "clean")
            self.assertEqual(git(snapshot, "rev-parse", "HEAD"), revision)
            self.assertEqual((snapshot / "reports/historical-input.txt").read_bytes(), expected)
            self.assertEqual(git(snapshot, "status", "--porcelain"), "")
            return type("Audit", (), {"revision": CLEAN_OLD})()

        with mock.patch.object(bump, "audit_repository", side_effect=audit):
            self.assertEqual(bump.clean_pin_at_revision(ir, revision), CLEAN_OLD)
        self.assertFalse(evidence.exists(), "historical audit must not expand the live sibling")
        self.assertEqual(git(ir, "config", "--get", "core.sparseCheckout"), "true")
        self.assertEqual(git(ir, "rev-parse", "HEAD"), revision)
        self.assertEqual(git(ir, "status", "--porcelain"), "")

    def test_external_manifest_edit_survives_rollback(self):
        self.mode("external-edit")
        with self.assertRaisesRegex(RuntimeError, "concurrent edits"):
            bump.update(self.root, self.new_ir, self.new_vc)
        changed = self.root / "driver/Cargo.toml"
        self.assertTrue(changed.read_text().endswith("# external edit\n"))
        for path, contents in self.before.items():
            if path != changed:
                self.assertEqual(path.read_bytes(), contents)

    @unittest.skipUnless(os.name == "posix", "POSIX process ownership")
    def test_interrupt_reaps_writer_before_rollback(self):
        self.mode("interrupt")
        result = subprocess.run([sys.executable, str(SCRIPT), self.new_ir, self.new_vc,
                                 "--root", str(self.root)], capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 130, result.stderr)
        self.assert_restored()
        pid = int((self.root / ".child-pid").read_text())
        with self.assertRaises(ProcessLookupError):
            os.kill(pid, 0)

    @unittest.skipUnless(os.name == "posix", "POSIX process ownership")
    def test_exited_leader_cannot_leave_a_late_lock_writer(self):
        import time
        self.mode("late-writer")
        try:
            with self.assertRaises(ValueError):
                bump.update(self.root, self.new_ir, self.new_vc)
            time.sleep(0.5)
            self.assert_restored()
        finally:
            pid_file = self.root / ".late-pid"
            if pid_file.exists():
                try:
                    os.kill(int(pid_file.read_text()), signal.SIGKILL)
                except ProcessLookupError:
                    pass

    @unittest.skipUnless(os.name == "posix", "POSIX process ownership")
    def test_repeated_stop_during_rollback_does_not_interrupt_restoration(self):
        self.mode("locked-failure")
        wrapper = self.base / "stop-during-rollback.py"
        wrapper.write_text('''import importlib.util, os, signal, sys
from pathlib import Path
script, root, ir, vc = sys.argv[1:]
sys.path.insert(0, str(Path(script).parent))
spec = importlib.util.spec_from_file_location("rollback_fixture", script)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
original = module.write_atomic
stopped = False
def write(path, data):
    global stopped
    if (Path(root) / ".validation-failed").exists() and not stopped:
        stopped = True
        os.kill(os.getpid(), signal.SIGTERM)
        os.kill(os.getpid(), signal.SIGINT)
    original(path, data)
module.write_atomic = write
sys.argv = [script, ir, vc, "--root", root]
raise SystemExit(module.main())
''')
        result = subprocess.run([sys.executable, str(wrapper), str(SCRIPT), str(self.root),
                                 self.new_ir, self.new_vc], capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assert_restored()


@unittest.skipUnless(sys.platform == "darwin", "native APFS clonefile optimization")
class CopyOnWriteSnapshot(unittest.TestCase):
    def setUp(self):
        parent = Path(tempfile.gettempdir()) / ".ubd"
        parent.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="mc-cow-", dir=parent)
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "ir"
        self.root.mkdir()
        git(self.root, "init", "-q")
        manifest = "[workspace.dependencies]\n" + "\n".join(
            f'{name} = {{ git = "{bump.FAMILIES["clean"].url}", rev = "{CLEAN_OLD}" }}'
            for name in ("clean-kernel", "clean-olean", "clean-mathverse")
        )
        (self.root / "Cargo.toml").write_text(manifest)
        (self.root / "reports").mkdir()
        (self.root / "reports/proof.bin").write_bytes(bytes(range(256)))
        (self.root / "old-only").write_text("retained old bytes")
        (self.root / "tool").write_text("#!/bin/sh\nexit 0\n")
        (self.root / "tool").chmod(0o755)
        (self.root / "link").symlink_to("Cargo.toml")
        self.old = commit(self.root)
        (self.root / "Cargo.toml").write_text(manifest.replace(CLEAN_OLD, CLEAN_NEW))
        (self.root / "reports/proof.bin").write_bytes(b"new proof")
        (self.root / "old-only").unlink()
        (self.root / "new-only").write_text("new bytes")
        self.new = commit(self.root)
        self.home = self.base / "cache"
        self.donor = self.home / "git/checkouts/trust-ir-fixture/donor"
        self.donor.parent.mkdir(parents=True)
        git(self.base, "clone", "-q", str(self.root), str(self.donor))
        self.snapshot = self.base / "snapshot"
        git(self.root, "worktree", "add", "--detach", "--no-checkout", "-q",
            str(self.snapshot), self.old)
        self.addCleanup(lambda: subprocess.run(
            ["git", "-C", str(self.root), "worktree", "remove", "--force", str(self.snapshot)],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))

    def reference(self):
        with mock.patch.dict(os.environ, {"CARGO_HOME": str(self.home)}):
            return bump.cached_snapshot_reference(self.root, self.old, self.base.stat().st_dev)

    def test_full_historical_tree_and_real_pin_audit_match(self):
        reference = self.reference()
        self.assertEqual(reference, (self.donor, self.new))
        bump.clone_snapshot_reference(self.root, self.old, self.snapshot, reference)
        self.assertEqual(bump.audit_repository(self.snapshot, "clean").revision, CLEAN_OLD)
        for name in git(self.root, "ls-tree", "-r", "--name-only", self.old).splitlines():
            path = self.snapshot / name
            expected = subprocess.check_output(["git", "-C", str(self.root), "show", self.old + ":" + name])
            actual = os.fsencode(os.readlink(path)) if path.is_symlink() else path.read_bytes()
            self.assertEqual(actual, expected, name)
        self.assertFalse((self.snapshot / "new-only").exists())
        self.assertTrue((self.snapshot / "tool").stat().st_mode & 0o111)
        self.assertEqual(git(self.donor, "rev-parse", "HEAD"), self.new)
        self.assertEqual(git(self.donor, "status", "--porcelain"), "")

    def test_dirty_reference_is_not_used(self):
        (self.donor / "reports/proof.bin").write_bytes(b"changed")
        self.assertIsNone(self.reference())

    def test_unsupported_filesystem_keeps_complete_historical_checkout(self):
        def unsupported(_root, _revision, snapshot, _reference):
            (snapshot / "partial-clone").write_text("must be removed")
            raise bump.SnapshotCloneUnavailable("fixture filesystem")

        with mock.patch.dict(os.environ, {"CARGO_HOME": str(self.home)}), \
                mock.patch.object(bump, "clone_snapshot_reference", side_effect=unsupported):
            self.assertEqual(bump.clean_pin_at_revision(self.root, self.old), CLEAN_OLD)
        self.assertEqual(git(self.donor, "status", "--porcelain"), "")

    def test_sparse_missing_reference_is_not_used(self):
        git(self.donor, "update-index", "--skip-worktree", "reports/proof.bin")
        (self.donor / "reports/proof.bin").unlink()
        self.assertIsNone(self.reference())

    def test_corrupted_copy_is_rejected_by_git_before_audit(self):
        real_git = bump.git

        def corrupt_before_refresh(root, *arguments):
            if "update-index" in arguments:
                (self.snapshot / "reports/proof.bin").write_bytes(b"corrupted copy")
            return real_git(root, *arguments)

        with mock.patch.object(bump, "git", side_effect=corrupt_before_refresh):
            with self.assertRaises(subprocess.CalledProcessError):
                bump.clone_snapshot_reference(self.root, self.old, self.snapshot,
                                              (self.donor, self.new))


if __name__ == "__main__":
    unittest.main()
