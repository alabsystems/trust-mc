#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Update the TrustIR/VC manifests, transitive Clean tuple and lock together.

TrustIR must be clean at the requested revision. The VC checkout may be a clean
descendant of its frozen pin; the normal shared-pin gate judges that drift.
This is a preparation transaction, not a substitute for check-shared-pins.sh or
the landing gate's live-main, frozen-content and qualification checks.
"""

from __future__ import annotations

import argparse
import copy
import errno
from contextlib import contextmanager
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

from check_first_party_git_pins import (
    FAMILIES,
    _dependency_sections,
    _tracked_manifests,
    audit_repository,
    toml_loads,
)
from host_room import _wait_child_exit
from git_authority_environment import git_environment, git_transport_environment


REVISION = re.compile(r"[0-9a-f]{40}")


class MetadataOwnershipLost(RuntimeError):
    """No rollback is safe while a lost writer may still modify the lock."""


class SnapshotCloneUnavailable(RuntimeError):
    """The filesystem cannot clone files; the complete checkout remains valid."""


class TransactionSignals:
    def __enter__(self):
        self.aborting = False
        self.deferred = False
        self.pending = False
        self.previous = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
        for sig in self.previous:
            signal.signal(sig, self.stop)
        return self

    def stop(self, _signum, _frame):
        if self.aborting:
            return
        if self.deferred:
            self.pending = True
        else:
            self.aborting = True
            raise KeyboardInterrupt("pin transaction interrupted")

    @contextmanager
    def publish_child(self):
        self.deferred = True
        try:
            yield
        finally:
            self.deferred = False
            if self.pending and not self.aborting:
                self.pending = False
                self.aborting = True
                raise KeyboardInterrupt("pin transaction interrupted during launch")

    def __exit__(self, *_error):
        for sig, handler in self.previous.items():
            signal.signal(sig, handler)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), *arguments], text=True, env=git_environment()
    ).strip()


def clean_revision(root: Path, expected: str, *, frozen: bool = False) -> str:
    head = git(root, "rev-parse", "HEAD")
    if frozen:
        git(root, "merge-base", "--is-ancestor", expected, head)
    else:
        require(head == expected, f"{root}: HEAD differs from requested pin")
    require(not git(root, "status", "--porcelain"), f"{root}: sibling checkout is dirty")
    return head


def write_atomic(path: Path, data: bytes) -> None:
    """An interrupted write must leave either complete image for rollback."""
    mode = path.stat().st_mode & 0o777
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.pin-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as output:
            os.fchmod(output.fileno(), mode)
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def manifest_update(original: bytes, pins: dict[str, tuple[str, str]]) -> bytes:
    text = original.decode("utf-8")
    expected = copy.deepcopy(toml_loads(text))
    replacements: dict[str, tuple[str, int]] = {}
    for _, dependencies in _dependency_sections(expected):
        for specification in dependencies.values():
            if not isinstance(specification, dict):
                continue
            for family, (old, new) in pins.items():
                if specification.get("git") != FAMILIES[family].url:
                    continue
                require(specification.get("rev") == old, f"{family}: inconsistent old revision")
                previous, count = replacements.get(old, (new, 0))
                require(previous == new, "one old revision names two different requested authorities")
                replacements[old] = (new, count + 1)
                specification["rev"] = new
    for old, (new, count) in replacements.items():
        # Refuse an ambiguous textual rewrite (including a matching comment or
        # unrelated revision). Reparse afterward to preserve all other fields.
        pattern = re.compile(rf"(\brev\s*=\s*)([\"']){re.escape(old)}\2")
        text, changed = pattern.subn(lambda match: match[1] + match[2] + new + match[2], text)
        require(changed == count, "cannot identify only the requested manifest revision fields")
    require(toml_loads(text) == expected, "manifest rewrite changed another field")
    return text.encode("utf-8")


def tuple_update(original: bytes, pins: dict[str, tuple[str, str]]) -> bytes:
    text = original.decode("utf-8")
    expected = copy.deepcopy(toml_loads(text))
    for table, (old, new) in pins.items():
        require(expected.get(table, {}).get("rev") == old, f"tuple [{table}].rev disagrees with the old pin")
        header = re.search(rf"(?m)^[ \t]*\[{re.escape(table)}\][ \t]*(?:#[^\r\n]*)?\r?$", text)
        require(header is not None, f"cannot locate tuple [{table}]")
        following = re.search(r"(?m)^[ \t]*\[", text[header.end():])
        end = header.end() + following.start() if following else len(text)
        body, count = re.subn(
            rf"(?m)^([ \t]*rev[ \t]*=[ \t]*)([\"']){re.escape(old)}\2([ \t]*(?:#[^\r\n]*)?\r?)$",
            lambda match: match[1] + match[2] + new + match[2] + match[3],
            text[header.end():end],
        )
        require(count == 1, f"cannot identify exact tuple [{table}].rev")
        text = text[:header.end()] + body + text[end:]
        expected[table]["rev"] = new
    require(toml_loads(text) == expected, "tuple rewrite changed another authority")
    return text.encode("utf-8")


def resolve_targo(root: Path) -> str:
    result = subprocess.run(
        [str(root / "scripts/resolve-trust-tool.sh"), "targo"],
        cwd=root, check=True, capture_output=True, text=True,
    )
    targo = result.stdout.strip()
    require(bool(targo) and Path(targo).is_file() and os.access(targo, os.X_OK),
            "Trust resolver did not return an executable targo")
    subprocess.run([targo, "--unverified", "--version"], cwd=root, check=True,
                   capture_output=True, text=True, timeout=30)
    return targo


def run_metadata(root: Path, targo: str, signals: TransactionSignals, *, locked: bool) -> dict:
    """Reap the owned writer before an interrupt can restore its lockfile."""
    arguments = [targo, "metadata", "--format-version", "1"]
    if locked:
        arguments.append("--locked")
    process = None
    reader = None
    output = []
    read_errors = []
    ownership_lost = False
    observed_exit = False

    def read():
        try:
            with process.stdout:
                output.append(process.stdout.read())
        except BaseException as error:
            read_errors.append(error)

    def finish():
        nonlocal ownership_lost
        if process is not None and not ownership_lost:
            if process.returncode is None:
                # No observer above reaps. Even on ordinary completion, keep
                # the leader's PID until its entire owned group is stopped.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except PermissionError as error:
                    # Darwin reports EPERM for a group containing only zombies.
                    # Do not confuse that with an unkillable live descendant.
                    try:
                        listing = subprocess.run(
                            ["ps", "-axo", "pid=,pgid=,stat="],
                            capture_output=True, text=True, timeout=10, check=True,
                        )
                    except (OSError, subprocess.SubprocessError) as inspection_error:
                        ownership_lost = True
                        if observed_exit:
                            process.wait()
                        raise MetadataOwnershipLost("metadata group could not be inspected; files retained") from inspection_error
                    members = [row.split() for row in listing.stdout.splitlines()
                               if len(row.split()) == 3 and row.split()[1] == str(process.pid)]
                    if not members or any(row[2][0] not in "ZXx" for row in members):
                        ownership_lost = True
                        if observed_exit:
                            process.wait()
                        raise MetadataOwnershipLost("could not stop every metadata writer; files retained") from error
                process.wait()
            if reader is not None:
                reader.join()

    try:
        with signals.publish_child():
            process = subprocess.Popen(arguments, cwd=root, stdout=subprocess.PIPE,
                                       text=True, start_new_session=True,
                                       env=git_transport_environment(root))
            reader = threading.Thread(target=read, daemon=True)
            reader.start()
        try:
            _wait_child_exit(process.pid)
            observed_exit = True
        except ChildProcessError as error:
            ownership_lost = True
            raise MetadataOwnershipLost("metadata writer ownership lost; files retained, no unsafe rollback") from error
        finish()
        if process.returncode:
            raise subprocess.CalledProcessError(process.returncode, arguments)
        if read_errors:
            raise ValueError("metadata output could not be read") from read_errors[0]
        return json.loads("".join(output))
    except BaseException:
        # The same scope remains installed through the caller's rollback.
        signals.aborting = True
        finish()
        raise


def cached_snapshot_reference(root: Path, revision: str, device: int) -> tuple[Path, str] | None:
    """Choose complete immutable Cargo source for a physical clone, not a pin."""
    if sys.platform != "darwin":
        return None
    home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))

    def tree_entries(at: str) -> dict[bytes, tuple[bytes, bytes, int]]:
        raw = subprocess.check_output(["git", "-C", str(root), "ls-tree", "-rlz", at],
                                      env=git_environment())
        result = {}
        for row in raw.split(b"\0"):
            if row:
                header, name = row.split(b"\t", 1)
                mode, _kind, identity, size = header.split()
                result[name] = (mode, identity, int(size) if size.isdigit() else 0)
        return result

    target = tree_entries(revision)
    choices = []
    for candidate in (home / "git" / "checkouts").glob("trust-ir-*/*"):
        if (not (candidate / ".git").exists() or candidate.is_symlink()
                or candidate.stat().st_dev != device):
            continue
        try:
            head = git(candidate, "rev-parse", "HEAD")
            known = subprocess.run(
                ["git", "-C", str(root), "cat-file", "-e", head + "^{commit}"],
                env=git_environment(), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            if known.returncode:
                continue
            if git(candidate, "status", "--porcelain", "--untracked-files=no"):
                continue
            if set(git(candidate, "ls-files", "--others").splitlines()) - {".cargo-ok"}:
                continue
            if any(line.startswith("S ") for line in git(candidate, "ls-files", "-v").splitlines()):
                continue
            entries = git(candidate, "ls-files", "--stage").splitlines()
            if any(line.startswith("160000 ") for line in entries):
                continue
            source = tree_entries(head)
            changed = [name for name, value in target.items()
                       if source.get(name) != value]
            # Prefer retained bytes, not just a low path count: one changed
            # historical blob can be much larger than thousands of sources.
            written = sum(target[name][2] for name in changed)
            choices.append((written, len(changed), str(candidate), head))
        except subprocess.CalledProcessError:
            continue
    if not choices:
        return None
    _, _, directory, head = min(choices)
    return Path(directory), head


def clone_snapshot_reference(root: Path, revision: str, snapshot: Path,
                             reference: tuple[Path, str]) -> None:
    """Clone all tracked bytes, then let Git apply and verify the exact delta."""
    import ctypes

    source, head = reference
    require(git(source, "rev-parse", "HEAD") == head, "snapshot reference moved")
    require(not git(source, "status", "--porcelain", "--untracked-files=no"),
            "snapshot reference became dirty")
    clonefile = ctypes.CDLL("/usr/lib/libSystem.B.dylib", use_errno=True).clonefile
    clonefile.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_int]
    clonefile.restype = ctypes.c_int
    raw = subprocess.check_output(["git", "-C", str(root), "ls-tree", "-rz", head],
                                  env=git_environment())
    for row in raw.split(b"\0"):
        if not row:
            continue
        header, encoded = row.split(b"\t", 1)
        mode, kind, _identity = header.decode("ascii").split()
        relative = Path(os.fsdecode(encoded))
        require(not relative.is_absolute() and
                not any(part in ("..", ".git") for part in relative.parts),
                "unsafe snapshot reference path")
        require(kind == "blob" and mode in ("100644", "100755", "120000"),
                "unsupported snapshot reference entry")
        original, target = source / relative, snapshot / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if mode == "120000":
            require(original.is_symlink(), "snapshot reference lost a symlink")
            target.symlink_to(os.readlink(original))
        else:
            require(original.is_file() and not original.is_symlink(),
                    "snapshot reference lost a regular file")
            if clonefile(os.fsencode(original), os.fsencode(target), 0) != 0:
                error = ctypes.get_errno()
                if error in (errno.ENOTSUP, errno.EOPNOTSUPP, errno.ENOSYS, errno.EXDEV):
                    raise SnapshotCloneUnavailable(os.strerror(error))
                raise OSError(error, os.strerror(error), str(original))
            target.chmod(0o755 if mode == "100755" else 0o644)
    options = ("-c", "core.sparseCheckout=false", "-c", "core.sparseCheckoutCone=false")
    git(snapshot, *options, "read-tree", head)
    git(snapshot, *options, "update-index", "--really-refresh")
    git(snapshot, *options, "read-tree", "-u", "-m", head, revision)
    require(git(snapshot, "rev-parse", "HEAD") == revision and
            not git(snapshot, *options, "status", "--porcelain"),
            "physical historical snapshot differs from its exact Git revision")
    require(git(source, "rev-parse", "HEAD") == head and
            not git(source, "status", "--porcelain", "--untracked-files=no"),
            "snapshot reference changed during cloning")


def clean_pin_at_revision(root: Path, revision: str) -> str:
    """Read the old authority from Git, not from the already advanced sibling."""
    # The selected producer's sealed-source audit needs its complete original
    # source and committed Git identity, not a synthesized manifest-only tree.
    with tempfile.TemporaryDirectory(prefix="mc-old-ir-source-") as directory:
        snapshot = Path(directory) / "source"
        reference = cached_snapshot_reference(root, revision, Path(directory).stat().st_dev)
        # Worktree creation can inherit the caller's sparse view. This audit
        # needs the complete historical source, including its sealed reports;
        # override checkout filtering only for this temporary worktree.
        git(root, "-c", "core.hooksPath=/dev/null",
            "-c", "core.sparseCheckout=false", "-c", "core.sparseCheckoutCone=false", "worktree", "add",
            "--detach", "--quiet", *(["--no-checkout"] if reference else []), str(snapshot), revision)
        try:
            if reference:
                print(f"bump-shared-pins: clone cached source {reference[1]} for {revision}", flush=True)
                try:
                    clone_snapshot_reference(root, revision, snapshot, reference)
                except SnapshotCloneUnavailable:
                    # Remove only this transaction's private tree, including
                    # any already-cloned paths, before the original complete
                    # checkout. An unsupported filesystem loses no capability.
                    git(root, "worktree", "remove", "--force", str(snapshot))
                    git(root, "-c", "core.hooksPath=/dev/null",
                        "-c", "core.sparseCheckout=false", "-c", "core.sparseCheckoutCone=false",
                        "worktree", "add", "--detach", "--quiet", str(snapshot), revision)
            result = audit_repository(snapshot, "clean").revision
            print(f"bump-shared-pins: historical source audit passed for {revision}", flush=True)
            return result
        finally:
            git(root, "worktree", "remove", "--force", str(snapshot))


def lock_projection(document: dict, affected: set[tuple]) -> dict:
    packages = document.get("package", [])
    indexed = {(p["name"], p["version"], p.get("source", "")): p for p in packages}
    require(len(indexed) == len(packages), "duplicate package identities in lockfile")

    def dependency_key(value: str) -> tuple:
        match = re.fullmatch(r"([^ ]+)(?: ([^ ]+))?(?: \((.*)\))?", value)
        require(match is not None, f"cannot identify locked dependency {value!r}")
        name, version, source = match.groups()
        candidates = [key for key in indexed if key[0] == name
                      and (version is None or key[1] == version)
                      and (source is None or key[2] == source)]
        require(len(candidates) == 1, f"ambiguous locked dependency {value!r}")
        return candidates[0]

    edges = {key: [dependency_key(value) for value in package.get("dependencies", [])]
             for key, package in indexed.items()}
    roots = [key for key in indexed if key[0] in (
        "trust-ir", "trust-ir-build", "trust-vc-merge-contract"
    ) or key[2].startswith(f"git+{FAMILIES['clean'].url}?")]
    pending = list(roots)
    while pending:
        key = pending.pop()
        if key in affected:
            continue
        affected.add(key)
        pending.extend(edges[key])
    return {"indexed": indexed, "edges": edges}


def validate_lock_change(before: bytes, after: bytes) -> None:
    old, new = toml_loads(before.decode()), toml_loads(after.decode())
    require({k: v for k, v in old.items() if k != "package"}
            == {k: v for k, v in new.items() if k != "package"}, "unrelated lockfile metadata changed")
    affected: set[tuple] = set()
    left = lock_projection(old, affected)
    # Traverse both graphs independently: a common root must not stop the new
    # traversal before its newly selected transitive dependencies are visited.
    new_affected: set[tuple] = set()
    right = lock_projection(new, new_affected)
    affected.update(new_affected)
    for key in left["indexed"].keys() & right["indexed"].keys():
        require({k: v for k, v in left["indexed"][key].items() if k != "dependencies"}
                == {k: v for k, v in right["indexed"][key].items() if k != "dependencies"},
                f"locked package metadata changed for {key[0]}")
    def stable_edge(key):
        name, version, source = key
        if name in ("trust-ir", "trust-ir-build", "trust-vc-merge-contract") or source.startswith(
            f"git+{FAMILIES['clean'].url}?"
        ):
            return (name, "<updated-authority>", "")
        return key
    def outside(graph):
        return {key: sorted(stable_edge(dep) for dep in graph["edges"][key])
                for key in graph["indexed"] if key not in affected}
    require(outside(left) == outside(right), "lock update changed an unrelated dependency")


def validate_resolution(metadata: dict, root: Path, vc: str, clean: str) -> None:
    packages = metadata.get("packages")
    require(isinstance(packages, list), "metadata has no package inventory")
    for name, expected in (
        ("trust-ir", root.parent / "trust-ir/crates/trust-ir/Cargo.toml"),
        ("trust-ir-build", root.parent / "trust-ir/crates/trust-ir-build/Cargo.toml"),
    ):
        rows = [package for package in packages if package.get("name") == name]
        require(len(rows) == 1 and rows[0].get("source") is None
                and Path(rows[0]["manifest_path"]).resolve() == expected.resolve(),
                f"{name} did not resolve uniquely to the selected sibling")
    for name, family, revision in (
        ("trust-vc-merge-contract", "trust-vc", vc), ("clean-kernel", "clean", clean),
    ):
        rows = [package for package in packages if package.get("name") == name]
        source = f"git+{FAMILIES[family].url}?rev={revision}#{revision}"
        require(len(rows) == 1 and rows[0].get("source") == source,
                f"{name} did not resolve uniquely to exact Git authority {revision}")


def _update(root: Path, ir: str, vc: str, signals: TransactionSignals) -> bool:
    for revision in (ir, vc):
        require(REVISION.fullmatch(revision) is not None and revision != "0" * 40,
                "pins must be nonzero full lowercase commit hashes")
    clean_revision(root.parent / "trust-ir", ir)
    vc_head = clean_revision(root.parent / "trust-vc", vc, frozen=True)
    old_ir = audit_repository(root, "trust-ir").revision
    old_vc = audit_repository(root, "trust-vc").revision
    clean = audit_repository(root.parent / "trust-ir", "clean").revision
    tuple_path = root / "tools/tuple.toml"
    tuple_bytes = tuple_path.read_bytes()
    old_clean = toml_loads(tuple_bytes.decode("utf-8")).get("clean", {}).get("rev")
    require(isinstance(old_clean, str) and REVISION.fullmatch(old_clean) is not None,
            "tuple has no full Clean revision")
    require(old_clean == clean_pin_at_revision(root.parent / "trust-ir", old_ir),
            "old tuple Clean pin disagrees with the old TrustIR commit")
    prepared = {}
    for path in _tracked_manifests(root):
        before = path.read_bytes()
        after = manifest_update(before, {"trust-ir": (old_ir, ir), "trust-vc": (old_vc, vc)})
        if before != after:
            require(not path.is_symlink(), f"refusing to edit a symlink: {path}")
            prepared[path] = (before, after)
    new_tuple = tuple_update(tuple_bytes, {
        "trust_ir": (old_ir, ir), "trust_vc": (old_vc, vc), "clean": (old_clean, clean),
    })
    if new_tuple != tuple_bytes:
        require(not tuple_path.is_symlink(), "refusing to edit a symlinked tuple")
        prepared[tuple_path] = (tuple_bytes, new_tuple)
    lock = root / "Cargo.lock"
    require(lock.is_file() and not lock.is_symlink(), "a regular root Cargo.lock is required")
    lock_before = lock.read_bytes()
    targo = resolve_targo(root)
    for path, (before, _) in prepared.items():
        require(path.read_bytes() == before, f"{path}: changed while preparing transaction")
    require(lock.read_bytes() == lock_before, "lock changed while preparing transaction")
    try:
        for path, (_, after) in prepared.items():
            write_atomic(path, after)
        require(audit_repository(root, "trust-ir").revision == ir, "TrustIR audit failed")
        require(audit_repository(root, "trust-vc").revision == vc, "VC audit failed")
        # Refresh through the authenticated frontend, then independently require
        # locked resolution. No lockfile text is synthesized by this helper.
        run_metadata(root, targo, signals, locked=False)
        metadata = run_metadata(root, targo, signals, locked=True)
        validate_resolution(metadata, root, vc, clean)
        validate_lock_change(lock_before, lock.read_bytes())
        clean_revision(root.parent / "trust-ir", ir)
        clean_revision(root.parent / "trust-vc", vc_head)
        for path, (_, after) in prepared.items():
            require(path.read_bytes() == after, f"{path}: changed during metadata validation")
    except BaseException as error:
        signals.aborting = True
        if isinstance(error, MetadataOwnershipLost):
            raise
        conflicts = []
        for path, (before, after) in prepared.items():
            try:
                if path.read_bytes() in (before, after):
                    write_atomic(path, before)
                else:
                    conflicts.append(str(path))
            except OSError:
                conflicts.append(str(path))
        try:
            write_atomic(lock, lock_before)
        except OSError:
            conflicts.append(str(lock))
        if conflicts:
            raise RuntimeError("rollback preserved concurrent edits to: " + ", ".join(conflicts))
        raise
    return bool(prepared) or lock.read_bytes() != lock_before


def update(root: Path, ir: str, vc: str) -> bool:
    with TransactionSignals() as signals:
        return _update(root, ir, vc, signals)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trust_ir_revision")
    parser.add_argument("trust_vc_revision")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    try:
        changed = update(args.root.resolve(), args.trust_ir_revision, args.trust_vc_revision)
    except KeyboardInterrupt:
        print("bump-shared-pins: interrupted; no qualification performed", file=sys.stderr)
        return 130
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f"bump-shared-pins: {error}", file=sys.stderr)
        return 1
    print("bump-shared-pins: " + ("updated manifests, Clean tuple and lock" if changed else "already current"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
