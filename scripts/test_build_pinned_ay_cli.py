#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Hermetic tests for scripts/build-pinned-ay-cli.sh, with a fake targo.

Each fixture is a throwaway trust-mc root (the script, ay_manifest_pin.py and
the python resolver copied beside a minimal Cargo.toml naming the pin), a
local git repository standing in for ../ay, a cache root, and a fake targo
that records its working directory and argv and writes a release/ay whose
--version names the commit its working tree is at.
"""

from __future__ import annotations

import os
import json
import hashlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/build-pinned-ay-cli.sh"

FAKE_TRUSTC = r"""#!/bin/sh
case "$*" in
  "-vV") printf '%s\n' "${FAKE_TRUSTC_VERSION:-trustc fixture compiler one}" "commit-hash: cccccccccccccccccccccccccccccccccccccccc" "host: aarch64-apple-darwin" ;;
  "--print sysroot") printf '%s\n' "$FAKE_SEAL" ;;
  *) exit 2 ;;
esac
"""

FAKE_RESOLVER = r"""#!/bin/sh
[ -z "${FAKE_RESOLVE_FAIL:-}" ] || exit 2
case "$1" in
  targo|trustc) printf '%s/bin/%s\n' "$FAKE_SEAL" "$1" ;;
  sysroot) printf '%s\n' "$FAKE_SEAL" ;;
  *) exit 2 ;;
esac
"""

FAKE_TARGO = r"""#!/bin/sh
if [ "$*" = '-Z unstable-options config get --format json' ]; then
  if [ -n "${FAKE_QUERY_FAIL:-}" ]; then printf 'credential=never-echo-this-secret\n' >&2; exit 31; fi
  "$FAKE_PYTHON" -c 'import json,os,tomllib; from pathlib import Path
c=tomllib.loads(Path(".cargo/config.toml").read_text())
def merge(a,b):
 for k,v in b.items():
  if isinstance(v,dict) and isinstance(a.get(k),dict): merge(a[k],v)
  else: a[k]=v
merge(c,json.loads(os.environ.get("FAKE_CARGO_CONFIG","{}")))
print(json.dumps(c))'
  exit $?
fi
printf '%s\n' "$PWD" >> "$FAKE_TARGO_LOG"
printf '%s\n' "$*" >> "$FAKE_TARGO_LOG"
[ -z "${FAKE_TARGO_FAIL:-}" ] || exit 19
[ "$RUSTC" = "$FAKE_SEAL/bin/trustc" ] || exit 20
[ -z "${RUSTC_WRAPPER:-}${RUSTC_WORKSPACE_WRAPPER:-}" ] || exit 21
target=""
previous=""
for argument in "$@"; do
  if [ "$previous" = "--target-dir" ]; then target="$argument"; fi
  previous="$argument"
done
[ -n "$target" ] || exit 3
manifest=""
previous=""
for argument in "$@"; do
  if [ "$previous" = "--manifest-path" ]; then manifest="$argument"; fi
  previous="$argument"
done
[ -n "$manifest" ] || exit 4
# The lane never runs cargo inside the worktree: a worktree cwd is a defect.
[ -f "$PWD/.cargo/config.toml" ] || exit 5
[ ! -e "$PWD/Cargo.toml" ] || exit 6
commit="${FAKE_TARGO_COMMIT:-$(git -C "$(dirname "$manifest")" rev-parse HEAD)}"
mkdir -p "$target/release"
cat > "$target/release/ay" <<EOS
#!/bin/sh
printf 'ay 0.0.0+build.1.%s@2026-09-12T00:00:00Z\nbuild.commit=%s\n' "$commit" "$commit"
EOS
chmod +x "$target/release/ay"
if [ -n "${FAKE_SWITCH_HEAD:-}" ]; then
  git -C "$(dirname "$manifest")" checkout --quiet --detach "$FAKE_SWITCH_HEAD"
fi
"""


# ay's own posture on every unit (the shape of ay 4cadc2bf1's config): the lane must not
# compile under it, and must keep what is not posture.
AY_POSTURE_CONFIG = """target-applies-to-host = false
[unstable]
target-applies-to-host = true
host-config = true
[host]
rustflags = ["-Ztrust-verify=on", "-Ztrust-policy=certify", "-Ztrust-ir-lower=strict"]
[target.'cfg(all())']
rustflags = ["-Ztrust-verify=on", "-Ztrust-ir-lower=strict"]
[target.aarch64-apple-darwin]
rustflags = ["-C", "target-cpu=native"]
[profile.release]
lto = "thin"
"""


def git(cwd: Path, *arguments: str) -> str:
    return subprocess.run(
        [
            "git", "-C", str(cwd),
            "-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid",
            "-c", "commit.gpgsign=false", "-c", "init.defaultBranch=main",
            *arguments,
        ],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def commit_file(repo: Path, name: str, text: str) -> str:
    (repo / name).write_text(text, encoding="utf-8")
    git(repo, "add", name)
    git(repo, "commit", "-q", "-m", name)
    return git(repo, "rev-parse", "HEAD")


def write_executable(path: Path, source: str) -> None:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


class Fixture:
    def __init__(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="build pinned ay cli ")
        base = Path(os.path.realpath(self.temporary.name))
        self.workspace = base / "ws"
        self.root = self.workspace / "trust-mc"
        self.ay = self.workspace / "ay"
        self.caches = base / "caches"
        self.log = base / "targo.log"
        self.seal = base / "fixture-seal"
        (self.seal / "bin").mkdir(parents=True)
        (self.seal / "lib").mkdir()
        (self.seal / "lib/librustc_driver-fixture.dylib").write_text("compiler driver one\n")
        self.targo = self.seal / "bin/targo"
        (self.root / "scripts/lib").mkdir(parents=True)
        for relative in (
            "scripts/build-pinned-ay-cli.sh",
            "scripts/ay_manifest_pin.py",
            "scripts/ay_cli_lane_config.py",
            "scripts/ay_cli_build_identity.py",
            "scripts/ay_cli_build_policy.py",
            "scripts/lib/python-with-toml.sh",
        ):
            shutil.copy2(ROOT / relative, self.root / relative)
        self.ay.mkdir(parents=True)
        git(self.ay, "init", "-q")
        self.first = commit_file(self.ay, "a.txt", "one\n")
        self.first = commit_file(self.ay, "LICENSE", "inert fixture license\n")
        (self.ay / ".cargo").mkdir()
        self.first = commit_file(self.ay, ".cargo/config.toml", AY_POSTURE_CONFIG)
        self.pin = self.first
        self.write_manifest(self.pin)
        write_executable(self.targo, FAKE_TARGO)
        write_executable(self.seal / "bin/trustc", FAKE_TRUSTC)
        write_executable(self.root / "scripts/resolve-trust-tool.sh", FAKE_RESOLVER)

    def write_manifest(self, pin: str) -> None:
        self.pin = pin
        rows = "\n".join(
            f'{name} = {{ version = "0.0.0", git = "https://github.com/alabsystems/ay.git", rev = "{pin}" }}'
            for name in ("ay-chc", "ay-core")
        )
        (self.root / "Cargo.toml").write_text(
            f"[workspace]\nmembers = []\n\n[workspace.dependencies]\n{rows}\n",
            encoding="utf-8",
        )

    @property
    def cache(self) -> Path:
        return self.caches / f"trust-mc-ay-cli-{self.pin[:9]}" / f"compiler-{self.base_builder['key']}"

    @property
    def base_builder(self) -> dict:
        result = subprocess.run(
            [sys.executable, str(self.root / "scripts/ay_cli_build_identity.py"),
             "identify", str(self.seal), str(self.seal / "bin/trustc"),
             str(self.targo), str(self.targo), str(getattr(self, "source_repo", self.ay)), self.pin],
            env=self.env(), capture_output=True, text=True, check=True,
        )
        return json.loads(result.stdout)

    @property
    def builder(self) -> dict:
        builder = self.base_builder
        lane = self.cache / "lane"
        if not lane.exists():
            return builder
        result = subprocess.run(
            [sys.executable, str(self.root / "scripts/ay_cli_build_identity.py"), "configure",
             json.dumps(builder), str(lane), str(self.cache / "src")],
            env=self.env(), capture_output=True, text=True, check=True,
        )
        return json.loads(result.stdout)

    @property
    def binary(self) -> Path:
        return self.cache / "release/ay"

    def env(self, **extra: str) -> dict[str, str]:
        env = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith(("TRUST_MC_", "CARGO_", "FAKE_", "GIT_"))
            and key not in ("RUSTFLAGS", "RUSTUP_TOOLCHAIN")
        }
        env.update(
            TRUST_MC_PYTHON=sys.executable,
            TRUST_MC_TARGO=str(self.targo),
            TRUST_MC_AY_CLI_CACHE_ROOT=str(self.caches),
            FAKE_TARGO_LOG=str(self.log),
            FAKE_SEAL=str(self.seal),
            FAKE_PYTHON=sys.executable,
            RUSTC=str(self.seal / "bin/trustc"),
        )
        env.update(extra)
        return env

    def run(self, *arguments: str, **extra: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.root / "scripts/build-pinned-ay-cli.sh"), *arguments],
            env=self.env(**extra),
            capture_output=True,
            text=True,
            timeout=120,
        )

    def targo_calls(self) -> list[tuple[str, str]]:
        if not self.log.exists():
            return []
        lines = self.log.read_text(encoding="utf-8").splitlines()
        return [(lines[i], lines[i + 1]) for i in range(0, len(lines), 2)]


class BuildPinnedAyCliTests(unittest.TestCase):
    def setUp(self) -> None:
        if shutil.which("git") is None:
            self.skipTest("git is not on PATH")
        self.fx = Fixture()
        self.addCleanup(self.fx.temporary.cleanup)

    def assert_ay_repo_untouched(self, head: str) -> None:
        self.assertEqual(git(self.fx.ay, "symbolic-ref", "HEAD"), "refs/heads/main")
        self.assertEqual(git(self.fx.ay, "rev-parse", "HEAD"), head)
        self.assertEqual(git(self.fx.ay, "status", "--porcelain"), "")

    def test_builds_in_a_pin_keyed_worktree_and_prints_the_binary(self) -> None:
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{self.fx.binary}\n")
        src = self.fx.cache / "src"
        self.assertEqual(git(src, "rev-parse", "HEAD"), self.fx.pin)
        calls = self.fx.targo_calls()
        self.assertEqual(len(calls), 1)
        cwd, argv = calls[0]
        # cargo runs from the lane directory, never from the worktree or ../ay, so ay's
        # .cargo/config.toml is not discovered; the manifest is named explicitly.
        self.assertEqual(os.path.realpath(cwd), os.path.realpath(self.fx.cache / "lane"))
        self.assertNotEqual(os.path.realpath(cwd), os.path.realpath(self.fx.ay))
        self.assertNotEqual(os.path.realpath(cwd), os.path.realpath(src))
        self.assertTrue(argv.startswith(
            f"--unverified build --locked --release -p ay --features cli "
            f"--manifest-path {src}/Cargo.toml --target-dir {self.fx.cache} "
        ), argv)
        self.assertIn('target-cpu=apple-m1', argv)
        self.assertNotIn(' --target ', argv)
        lane = (self.fx.cache / "lane/.cargo/config.toml").read_text(encoding="utf-8")
        body = "\n".join(line for line in lane.splitlines() if not line.startswith("#"))
        self.assertNotIn("-Ztrust", body)
        self.assertIn('rustflags = ["-C", "target-cpu=native"]', lane)
        self.assertIn('lto = "thin"', lane)
        self.assertIn("[host]\nrustflags = []", body)
        self.assertIn(self.fx.pin, subprocess.run(
            [str(self.fx.binary), "--version"], capture_output=True, text=True, check=True
        ).stdout)
        self.assert_ay_repo_untouched(self.fx.first)

    def test_a_worktree_without_a_cargo_config_gets_an_empty_lane_config(self) -> None:
        git(self.fx.ay, "rm", "-q", ".cargo/config.toml")
        git(self.fx.ay, "commit", "-q", "-m", "no config")
        bare = git(self.fx.ay, "rev-parse", "HEAD")
        self.fx.write_manifest(bare)
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.fx.cache / "lane/.cargo/config.toml").read_text(encoding="utf-8"), "")
        self.assertEqual(len(self.fx.targo_calls()), 1)

    def test_a_malformed_ay_cargo_config_refuses_before_targo_runs(self) -> None:
        (self.fx.ay / ".cargo/config.toml").write_text("[host\n", encoding="utf-8")
        git(self.fx.ay, "add", ".cargo/config.toml")
        git(self.fx.ay, "commit", "-q", "-m", "broken config")
        self.fx.write_manifest(git(self.fx.ay, "rev-parse", "HEAD"))
        result = self.fx.run()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unverified-lane cargo config", result.stderr)
        self.assertEqual(self.fx.targo_calls(), [])

    def test_second_run_reuses_the_binary_without_building(self) -> None:
        first = self.fx.run()
        second = self.fx.run()
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual(second.stdout, first.stdout)
        self.assertEqual(len(self.fx.targo_calls()), 1)

    def test_compiler_change_uses_another_cache_and_builds(self) -> None:
        first = self.fx.run()
        second = self.fx.run(FAKE_TRUSTC_VERSION="trustc fixture compiler two")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertNotEqual(first.stdout, second.stdout)
        self.assertEqual(len(self.fx.targo_calls()), 2)

    def test_compiler_bytes_change_even_with_same_version_uses_another_cache(self) -> None:
        first = self.fx.run()
        compiler = self.fx.seal / "bin/trustc"
        compiler.write_text(compiler.read_text() + "# changed compiler bytes\n")
        second = self.fx.run()
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertNotEqual(first.stdout, second.stdout)
        self.assertEqual(len(self.fx.targo_calls()), 2)

    def test_driver_change_with_same_launcher_and_version_changes_cache(self) -> None:
        first = self.fx.run()
        (self.fx.seal / "lib/librustc_driver-fixture.dylib").write_text("driver two\n")
        second = self.fx.run()
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertNotEqual(first.stdout, second.stdout)
        self.assertEqual(len(self.fx.targo_calls()), 2)

    def test_declared_driver_identity_does_not_hide_changed_installed_bytes(self) -> None:
        (self.fx.seal / "PROVENANCE").write_text(
            "artifact_driver_name=librustc_driver-fixture.dylib\n"
            "artifact_driver_sha256=" + "a" * 64 + "\n")
        first = self.fx.run()
        (self.fx.seal / "lib/librustc_driver-fixture.dylib").write_text("driver two\n")
        second = self.fx.run()
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertNotEqual(first.stdout, second.stdout)
        self.assertEqual(self.fx.builder["identity"]["toolchain"]["artifact_driver_sha256"], "a" * 64)

    def test_clean_head_switch_during_build_does_not_get_a_receipt(self) -> None:
        later = commit_file(self.fx.ay, "later.txt", "new commit\n")
        before = self.fx.cache
        result = self.fx.run(FAKE_SWITCH_HEAD=later)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("changed HEAD", result.stderr)
        self.assertFalse((before / "builder.json").exists())

    def test_check_path_validates_without_building(self) -> None:
        self.assertEqual(self.fx.run().returncode, 0)
        result = self.fx.run("--check-path")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{self.fx.binary}\n")
        self.assertEqual(len(self.fx.targo_calls()), 1)

    def test_receipt_records_gate_identity_and_binary_digest(self) -> None:
        import hashlib
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads((self.fx.cache / "builder.json").read_text())
        self.assertEqual(receipt["ay_commit"], self.fx.pin)
        self.assertEqual(receipt["lane"], "unverified")
        self.assertEqual(receipt["builder"], self.fx.builder)
        toolchain = receipt["builder"]["identity"]["toolchain"]
        self.assertEqual(toolchain["sysroot"], str(self.fx.seal))
        self.assertEqual(toolchain["trustc_vV_sha256"],
                         hashlib.sha256(b"trustc fixture compiler one\ncommit-hash: cccccccccccccccccccccccccccccccccccccccc\nhost: aarch64-apple-darwin\n").hexdigest())
        self.assertEqual(toolchain["installed_driver_sha256"],
                         hashlib.sha256(b"compiler driver one\n").hexdigest())
        self.assertEqual(receipt["binary_sha256"], hashlib.sha256(self.fx.binary.read_bytes()).hexdigest())

    def test_unrecorded_binary_is_rebuilt(self) -> None:
        self.assertEqual(self.fx.run().returncode, 0)
        (self.fx.cache / "builder.json").unlink()
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.fx.targo_calls()), 2)

    def test_changed_binary_cannot_reuse_its_receipt(self) -> None:
        self.assertEqual(self.fx.run().returncode, 0)
        self.fx.binary.write_text(self.fx.binary.read_text() + "# unrecorded bytes\n")
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.fx.targo_calls()), 2)

    def test_legacy_native_compiler_receipt_is_never_admitted(self) -> None:
        self.assertEqual(self.fx.run().returncode, 0)
        receipt = self.fx.cache / "builder.json"
        record = json.loads(receipt.read_text())
        record["schema"] = "trust-mc.ay-cli-build/v1"
        del record["builder"]["identity"]["build_policy"]
        del record["builder"]["configuration"]
        receipt.write_text(json.dumps(record))
        checked = self.fx.run("--check-path")
        self.assertNotEqual(checked.returncode, 0, checked.stderr)
        self.assertEqual(len(self.fx.targo_calls()), 1)
        self.assertEqual(self.fx.run().returncode, 0)
        self.assertEqual(len(self.fx.targo_calls()), 2)

    def test_resolved_config_change_refuses_cached_binary_then_rebuilds(self) -> None:
        self.assertEqual(self.fx.run().returncode, 0)
        before = json.loads((self.fx.cache / "builder.json").read_text())["builder"]["configuration"]
        config = json.dumps({"build": {"rustflags": ["--cfg", "changed_policy"]}})
        checked = self.fx.run("--check-path", FAKE_CARGO_CONFIG=config)
        self.assertNotEqual(checked.returncode, 0, checked.stderr)
        self.assertEqual(len(self.fx.targo_calls()), 1)
        self.assertEqual(self.fx.run(FAKE_CARGO_CONFIG=config).returncode, 0)
        self.assertEqual(len(self.fx.targo_calls()), 2)
        after = json.loads((self.fx.cache / "builder.json").read_text())["builder"]["configuration"]
        self.assertNotEqual(before["effective_config_sha256"], after["effective_config_sha256"])

    def test_policy_query_failure_never_exposes_config_diagnostics(self) -> None:
        result = self.fx.run(FAKE_QUERY_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exit 31", result.stderr)
        self.assertNotIn("never-echo", result.stderr + result.stdout)
        self.assertEqual(self.fx.targo_calls(), [])

    def test_recipe_change_changes_cache_key(self) -> None:
        original = self.fx.cache
        policy = self.fx.root / "scripts/ay_cli_build_policy.py"
        policy.write_text(policy.read_text() + "\n# changed recipe fixture\n")
        self.assertNotEqual(self.fx.cache, original)

    def test_native_target_routing_and_configured_flag_env_refuse(self) -> None:
        for config in ({"build": {"target": "aarch64-apple-darwin"}},
                       {"env": {"RUSTFLAGS": {"value": "-C target-cpu=native", "force": True}}}):
            with self.subTest(config=config):
                result = self.fx.run(FAKE_CARGO_CONFIG=json.dumps(config))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(self.fx.targo_calls(), [])

    def test_a_cached_binary_does_not_bypass_compiler_resolution(self) -> None:
        self.assertEqual(self.fx.run().returncode, 0)
        result = self.fx.run(FAKE_RESOLVE_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertEqual(len(self.fx.targo_calls()), 1)

    def test_foreign_targo_cannot_claim_the_pinned_compiler(self) -> None:
        foreign = self.fx.seal / "bin/other-targo"
        write_executable(foreign, FAKE_TARGO)
        result = self.fx.run(TRUST_MC_TARGO=str(foreign))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("pinned compiler's targo", result.stderr)
        self.assertEqual(self.fx.targo_calls(), [])

    def test_legacy_pin_only_cache_is_not_reused(self) -> None:
        legacy = self.fx.caches / f"trust-mc-ay-cli-{self.fx.pin[:9]}" / "release/ay"
        legacy.parent.mkdir(parents=True)
        write_executable(legacy, "#!/bin/sh\necho 'ay " + self.fx.pin + "'\n")
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{self.fx.binary}\n")
        self.assertEqual(len(self.fx.targo_calls()), 1)
        self.assertTrue(legacy.exists())

    def test_failed_build_does_not_leave_a_receipt(self) -> None:
        result = self.fx.run(FAKE_TARGO_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.fx.cache / "builder.json").exists())

    def test_build_uses_resolved_compiler_and_removes_wrappers(self) -> None:
        result = self.fx.run(RUSTC="/foreign/compiler", RUSTC_WRAPPER="/foreign/wrapper",
                             RUSTC_WORKSPACE_WRAPPER="/foreign/workspace-wrapper")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_a_binary_naming_another_commit_fails(self) -> None:
        result = self.fx.run(FAKE_TARGO_COMMIT="1" * 40)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn(self.fx.pin, result.stderr)

    def test_a_shared_prefix_is_not_the_full_pin(self) -> None:
        impostor = self.fx.pin[:9] + ("0" if self.fx.pin[9] != "0" else "1") + self.fx.pin[10:]
        result = self.fx.run(FAKE_TARGO_COMMIT=impostor)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")

    def test_a_stale_binary_under_the_key_is_rebuilt(self) -> None:
        self.fx.binary.parent.mkdir(parents=True)
        write_executable(self.fx.binary, "#!/bin/sh\necho 'ay 0.0.0+build.1." + "2" * 40 + "'\n")
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.fx.targo_calls()), 1)

    def test_a_dirty_cache_worktree_is_refused(self) -> None:
        src = self.fx.cache / "src"
        self.fx.cache.mkdir(parents=True)
        git(self.fx.ay, "worktree", "add", "--detach", str(src), self.fx.pin)
        (src / "stray.txt").write_text("x\n", encoding="utf-8")
        result = self.fx.run()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("dirty", result.stderr)
        self.assertEqual(self.fx.targo_calls(), [])

    def test_a_cache_worktree_at_another_commit_is_refused(self) -> None:
        second = commit_file(self.fx.ay, "b.txt", "two\n")
        self.fx.write_manifest(second)
        src = self.fx.cache / "src"
        self.fx.cache.mkdir(parents=True)
        git(self.fx.ay, "worktree", "add", "--detach", str(src), self.fx.first)
        result = self.fx.run()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not the pin", result.stderr)
        self.assertEqual(self.fx.targo_calls(), [])

    def test_a_pin_missing_locally_refuses_without_implicit_git_network(self) -> None:
        upstream = self.fx.workspace / "upstream"
        shutil.move(str(self.fx.ay), str(upstream))
        subprocess.run(
            ["git", "clone", "-q", str(upstream), str(self.fx.ay)], check=True, capture_output=True
        )
        later = commit_file(upstream, "c.txt", "three\n")
        self.fx.write_manifest(later)
        result = self.fx.run()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("native agh", result.stderr)
        self.assertEqual(self.fx.targo_calls(), [])
        self.assert_ay_repo_untouched(self.fx.first)

    def stage_bundle(self, name="bundle", compiler="c" * 40):
        destination = self.fx.workspace / name
        destination.mkdir()
        result = subprocess.run(
            [sys.executable, str(self.fx.root / "scripts/ay_cli_build_identity.py"), "stage-bundle",
             str(self.fx.binary), str(destination), self.fx.pin, str(self.fx.seal),
             str(self.fx.seal / "bin/trustc"), str(self.fx.targo), compiler],
            env=self.fx.env(), capture_output=True, text=True, timeout=30,
        )
        return result, destination

    def test_bundle_stages_checked_bytes_portable_origin_and_pinned_license(self):
        built = self.fx.run()
        self.assertEqual(built.returncode, 0, built.stderr)
        staged, root = self.stage_bundle()
        self.assertEqual(staged.returncode, 0, staged.stderr)
        self.assertEqual((root / "libexec/ay").read_bytes(), self.fx.binary.read_bytes())
        self.assertEqual((root / "libexec/ay-licenses/LICENSE").read_bytes(),
                         (self.fx.cache / "src/LICENSE").read_bytes())
        record = json.loads((root / "libexec/ay-origin.json").read_text())
        self.assertEqual(record["ay_commit"], self.fx.pin)
        self.assertEqual(record["compiler_commit"], "c" * 40)
        self.assertEqual(record["build_binary_sha256"], hashlib.sha256(self.fx.binary.read_bytes()).hexdigest())
        self.assertNotIn(str(self.fx.workspace.parent), json.dumps(record))
        self.assertNotIn("sysroot", record["compiler_identity"])

    def test_bundle_refuses_changed_binary_or_missing_complete_receipt(self):
        self.assertEqual(self.fx.run().returncode, 0)
        receipt = self.fx.cache / "builder.json"
        original = receipt.read_bytes()
        receipt.unlink()
        result, root = self.stage_bundle("missing-receipt")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exact source/compiler/binary", result.stderr)
        self.assertFalse((root / "libexec").exists())
        receipt.write_bytes(original)
        self.fx.binary.write_bytes(self.fx.binary.read_bytes() + b"\n# changed\n")
        result, _ = self.stage_bundle("changed-binary")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exact source/compiler/binary", result.stderr)

    def test_bundle_refuses_another_admitted_compiler(self):
        self.assertEqual(self.fx.run().returncode, 0)
        result, _ = self.stage_bundle(compiler="d" * 40)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("compiler differs", result.stderr)

    def test_bundle_rechecks_dirty_and_off_pin_version_even_with_matching_byte_receipt(self):
        self.assertEqual(self.fx.run().returncode, 0)
        for name, stamp in (("dirty", self.fx.pin + "-dirty"), ("off-pin", "d" * 40)):
            with self.subTest(case=name):
                write_executable(self.fx.binary, f"#!/bin/sh\nprintf 'ay 0.1.0+build.1.{stamp}\\n'\n")
                receipt = self.fx.cache / "builder.json"
                record = json.loads(receipt.read_text())
                record["binary_sha256"] = hashlib.sha256(self.fx.binary.read_bytes()).hexdigest()
                receipt.write_text(json.dumps(record))
                result, root = self.stage_bundle(name)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("dirty, off-pin or unstamped", result.stderr)
                self.assertFalse((root / "libexec").exists())

    def test_an_explicit_ay_repo_is_used(self) -> None:
        other = self.fx.workspace / "elsewhere-ay"
        shutil.move(str(self.fx.ay), str(other))
        result = self.fx.run(TRUST_MC_AY_REPO=str(other))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.fx.ay = other
        self.assertIn(str(self.fx.cache / "src"), git(other, "worktree", "list"))

    def test_the_unkeyed_cache_is_never_touched(self) -> None:
        unkeyed = self.fx.caches / "trust-mc-ay-cli/release/ay"
        unkeyed.parent.mkdir(parents=True)
        write_executable(unkeyed, "#!/bin/sh\necho 'ay 0.0.0+build.1." + self.fx.pin + "'\n")
        before = (unkeyed.read_bytes(), unkeyed.stat().st_mtime_ns)
        result = self.fx.run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotEqual(result.stdout.strip(), str(unkeyed))
        self.assertEqual((unkeyed.read_bytes(), unkeyed.stat().st_mtime_ns), before)
        self.assertEqual(len(self.fx.targo_calls()), 1)

    def test_print_path_builds_nothing(self) -> None:
        result = self.fx.run("--print-path")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{self.fx.binary}\n")
        self.assertFalse(self.fx.caches.exists())
        self.assertEqual(self.fx.targo_calls(), [])

    @unittest.skipUnless(sys.platform == "darwin", "the default cache root is ~/Library/Caches on macOS")
    def test_default_cache_root_is_the_user_cache(self) -> None:
        home = self.fx.workspace / "home"
        home.mkdir()
        env_home = {"HOME": str(home)}
        result = subprocess.run(
            [str(self.fx.root / "scripts/build-pinned-ay-cli.sh"), "--print-path"],
            env={k: v for k, v in self.fx.env(**env_home).items() if k != "TRUST_MC_AY_CLI_CACHE_ROOT"},
            capture_output=True,
            text=True,
            timeout=60,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            result.stdout,
            f"{home}/Library/Caches/trust-mc-ay-cli-{self.fx.pin[:9]}/compiler-{self.fx.builder['key']}/release/ay\n",
        )

    def test_unknown_arguments_exit_2(self) -> None:
        self.assertEqual(self.fx.run("--bogus").returncode, 2)
        self.assertEqual(self.fx.run("--print-path", "extra").returncode, 2)

    def test_a_manifest_without_a_pin_fails(self) -> None:
        (self.fx.root / "Cargo.toml").write_text("[workspace]\nmembers = []\n", encoding="utf-8")
        result = self.fx.run()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertEqual(self.fx.targo_calls(), [])


class RepositoryPinTests(unittest.TestCase):
    def test_print_path_follows_this_checkouts_cargo_pin(self) -> None:
        sys.path.insert(0, str(ROOT / "scripts"))
        try:
            from ay_manifest_pin import expected_ay_pin_from_cargo_toml
        finally:
            sys.path.pop(0)
        pin = expected_ay_pin_from_cargo_toml(ROOT)
        fixture = Fixture()
        self.addCleanup(fixture.temporary.cleanup)
        fixture.write_manifest(pin)
        authority = ROOT.parent / "ay"
        if subprocess.run(["git", "-C", str(authority), "cat-file", "-e", f"{pin}^{{commit}}"],
                          capture_output=True).returncode:
            self.skipTest("exact pinned AY source is not locally admitted beside this checkout")
        fixture.source_repo = authority
        result = fixture.run("--print-path", TRUST_MC_AY_REPO=str(authority))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{fixture.binary}\n")


if __name__ == "__main__":
    unittest.main()
