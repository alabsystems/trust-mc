#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Check the committed measurement tuple (tools/tuple.toml) against this host.

A counted Kani-corpus row names the exact inputs that produced it, and
tools/tuple.toml is that name, committed. This checker refuses the tuple when an
input it names is not what this workspace, its sibling checkouts or the resolved
Trust toolchain actually are. Every check runs, and each mismatch is reported
separately.

TRUST_MC_TRUST_TOOLCHAIN, when set, is honoured by scripts/resolve-trust-tool.sh
in place of rust-toolchain.toml's channel, so trust.commit and trust.build
compare the tuple with the toolchain it names, and --json records it as
trust.toolchain_override (null when unset).

The check is offline and read-only. scripts/check-ay-pin.sh and
scripts/check-shared-pins.sh additionally prove Cargo's resolution and
reachability from live main. Run through tools/tuple-check, which selects a
python with tomllib.
"""

from __future__ import annotations

from git_authority_environment import git_environment

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Callable, Mapping

if sys.version_info < (3, 11):
    sys.stderr.write(
        "tuple-check: error: python >= 3.11 is required for tomllib; "
        "run tools/tuple-check, which resolves one, or set AY_PYTHON\n"
    )
    raise SystemExit(2)

import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_first_party_git_pins import audit_repository  # noqa: E402
from development_seal import (  # noqa: E402
    DevelopmentSeal,
    IDENTITY_SCOPE,
    SealRefusal,
    verify as verify_development_seal,
)

TUPLE_SCHEMA = 1
DEVELOPMENT_TUPLE_SCHEMA = 2
REPORT_SCHEMA = 1
REVISION = re.compile(r"^[0-9a-f]{40}$")
CHANNEL = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
KANI_REV_DECLARATION = re.compile(
    r'^pub const DEFAULT_KANI_REV: &str = "([^"]*)";$', re.MULTILINE
)
LOCK_GIT_SOURCE = re.compile(
    r"^git\+(?P<url>[^?#]+)\?rev=(?P<rev>[0-9a-f]{40})#(?P<commit>[0-9a-f]{40})$"
)

# scripts/resolve-trust-tool.sh: a rustup toolchain name or an absolute seal
# directory resolved in place of rust-toolchain.toml's channel.
TRUST_TOOLCHAIN_OVERRIDE_ENV = "TRUST_MC_TRUST_TOOLCHAIN"

# tools/kani-domination/src/env.rs CORPUS_DIR_ENV: names the corpus checkout.
KANI_CORPUS_DIR_ENV = "KANI_DOMINATION_CORPUS_DIR"

PASS = "pass"
FAIL = "fail"
UNCHECKED = "unchecked"

# Report order. Tests pin it so a consumer can rely on it.
CHECK_IDS = (
    "trust.channel",
    "trust.commit",
    "trust.build",
    "frozen.channel",
    "ay.manifest",
    "ay.checkout",
    "trust-ir.manifest",
    "trust-ir.checkout",
    "trust-vc.manifest",
    "trust-vc.lock",
    "clean.manifest",
    "clean.lock",
    "kani.corpus",
    "kani.checkout",
    "kani.spec",
)

# table -> key -> kind. Unknown tables and keys are rejected so a typo cannot
# silently drop a field out of the comparison.
TUPLE_FIELDS: dict[str, dict[str, str]] = {
    "trust": {"rev": "rev", "build": "build", "channel": "channel"},
    "frozen_toolchain": {"channel": "channel"},
    "ay": {"rev": "rev"},
    "trust_ir": {"rev": "rev"},
    "trust_vc": {"rev": "rev"},
    "clean": {"rev": "rev"},
    "kani": {"corpus_rev": "rev", "spec_rev": "rev"},
}


class TupleError(ValueError):
    """The tuple file itself is unreadable or malformed (exit 2)."""


class Refusal(Exception):
    """An input a check compares could not be read; the message says which."""


@dataclass(frozen=True)
class MeasurementTuple:
    trust_rev: str
    trust_build: int | None
    trust_channel: str
    frozen_channel: str
    ay_rev: str
    trust_ir_rev: str
    trust_vc_rev: str
    clean_rev: str
    kani_corpus_rev: str
    kani_spec_rev: str
    document: dict[str, Any] = field(compare=False, repr=False)
    development_seal: DevelopmentSeal | None = None
    source_sha256: str = field(default="", compare=False, repr=False)


@dataclass(frozen=True)
class Check:
    id: str
    status: str
    expected: str | None
    actual: str | None
    source: str
    message: str


@dataclass(frozen=True)
class Layout:
    """Where the inputs live. Siblings follow Cargo.toml's ../ path patches."""

    repo_root: Path

    @property
    def ay_repo(self) -> Path:
        return self.repo_root.parent / "ay"

    @property
    def trust_ir_repo(self) -> Path:
        return self.repo_root.parent / "trust-ir"

    def kani_checkout(self, rev: str, environ: Mapping[str, str] | None = None) -> Path:
        """The Kani corpus checkout tools/kani-domination reads with no --kani-dir.

        Mirrors env.rs `corpus_dir(None, DEFAULT_KANI_REV)`: a non-empty
        $KANI_DOMINATION_CORPUS_DIR (relative to the current directory, as the
        runner resolves it), else `<user cache>/trust-mc/kani-domination/<rev>`,
        where the user cache is ~/Library/Caches on macOS and $XDG_CACHE_HOME or
        ~/.cache elsewhere. The corpus left <repo>/target on 2026-09-11 because
        cargo units there inherited trust-mc's own .cargo/config.toml; a
        checkout still under target/kani-domination/kani is never read.
        """
        env = os.environ if environ is None else environ
        override = env.get(KANI_CORPUS_DIR_ENV)
        if override:
            path = Path(override)
            return path if path.is_absolute() else Path.cwd() / path
        home = env.get("HOME") or None
        if sys.platform == "darwin":
            cache = Path(home) / "Library" / "Caches" if home else None
        else:
            xdg = env.get("XDG_CACHE_HOME") or None
            cache = Path(xdg) if xdg else (Path(home) / ".cache" if home else None)
        if cache is None:
            raise Refusal(
                "cannot place the Kani corpus checkout: HOME is unset and "
                f"{KANI_CORPUS_DIR_ENV} names no checkout"
            )
        return cache / "trust-mc" / "kani-domination" / rev

    @property
    def resolver(self) -> Path:
        return self.repo_root / "scripts" / "resolve-trust-tool.sh"

    @property
    def kani_spec_pins(self) -> Path:
        return self.repo_root / "tools" / "kani-spec" / "pins.toml"

    def kani_spec_manifest(self, rev: str) -> Path:
        return self.repo_root / "spec" / "kani" / rev / "manifest.json"


def load_tuple(path: Path) -> MeasurementTuple:
    try:
        source = path.read_bytes()
        document = tomllib.loads(source.decode("utf-8"))
    except OSError as error:
        raise TupleError(f"{path}: cannot read tuple: {error}") from error
    except tomllib.TOMLDecodeError as error:
        raise TupleError(f"{path}: tuple is not valid TOML: {error}") from error
    except UnicodeError as error:
        raise TupleError(f"{path}: tuple is not strict UTF-8: {error}") from error

    errors: list[str] = []
    schema = document.get("schema")
    if type(schema) is not int or schema not in (TUPLE_SCHEMA, DEVELOPMENT_TUPLE_SCHEMA):
        errors.append(f"schema must be {TUPLE_SCHEMA} or {DEVELOPMENT_TUPLE_SCHEMA}, found {schema!r}")
    fields_by_table = dict(TUPLE_FIELDS)
    development = schema == DEVELOPMENT_TUPLE_SCHEMA
    if development:
        fields_by_table["trust"] = {"rev": "rev", "channel": "channel", "identity": "development"}
    extra_tables = {"development_seal"} if development else set()
    for key in sorted(set(document) - set(fields_by_table) - {"schema"} - extra_tables):
        errors.append(f"unknown top-level key {key!r}")

    values: dict[str, Any] = {}
    for table, fields in fields_by_table.items():
        raw_table = document.get(table)
        if not isinstance(raw_table, dict):
            errors.append(f"missing [{table}] table")
            continue
        for key in sorted(set(raw_table) - set(fields)):
            errors.append(f"unknown key {table}.{key}")
        for key, kind in fields.items():
            value = raw_table.get(key)
            name = f"{table}.{key}"
            if kind == "rev":
                if (
                    not isinstance(value, str)
                    or REVISION.fullmatch(value) is None
                    or value == "0" * 40
                ):
                    errors.append(
                        f"{name} must be a nonzero 40-character lowercase hex "
                        f"revision, found {value!r}"
                    )
            elif kind == "build":
                if type(value) is not int or value <= 0:
                    errors.append(
                        f"{name} must be a positive integer seal build, found {value!r}"
                    )
            elif kind == "channel":
                if not isinstance(value, str) or CHANNEL.fullmatch(value) is None:
                    errors.append(f"{name} must be a toolchain channel name, found {value!r}")
            elif kind == "development" and value != "development":
                errors.append(f"{name} must explicitly be 'development', found {value!r}")
            values[name] = value
    seal = None
    if development:
        try:
            seal = DevelopmentSeal.parse(document.get("development_seal"))
        except SealRefusal as error:
            errors.append(str(error))
    if errors:
        raise TupleError("\n".join(f"{path}: {error}" for error in errors))
    return MeasurementTuple(
        trust_rev=values["trust.rev"],
        trust_build=values.get("trust.build"),
        trust_channel=values["trust.channel"],
        frozen_channel=values["frozen_toolchain.channel"],
        ay_rev=values["ay.rev"],
        trust_ir_rev=values["trust_ir.rev"],
        trust_vc_rev=values["trust_vc.rev"],
        clean_rev=values["clean.rev"],
        kani_corpus_rev=values["kani.corpus_rev"],
        kani_spec_rev=values["kani.spec_rev"],
        document=document,
        development_seal=seal,
        source_sha256=hashlib.sha256(source).hexdigest(),
    )


# --- input readers --------------------------------------------------------


def _run(argv: list[str], *, timeout: int = 120) -> str:
    shown = shlex.join(argv)
    try:
        completed = subprocess.run(
            argv, capture_output=True, text=True, timeout=timeout, check=False,
            env=git_environment() if argv[0] == "git" else None
        )
    except OSError as error:
        raise Refusal(f"`{shown}` could not run: {error}") from error
    except subprocess.TimeoutExpired as error:
        raise Refusal(f"`{shown}` timed out after {timeout}s") from error
    if completed.returncode != 0:
        lines = completed.stderr.strip().splitlines()
        detail = f": {lines[-1]}" if lines else ""
        raise Refusal(f"`{shown}` exited {completed.returncode}{detail}")
    return completed.stdout.strip()


def _git(repo: Path, *args: str) -> str:
    return _run(["git", "-C", str(repo), *args])


def _read_toml(path: Path) -> dict[str, Any]:
    try:
        return tomllib.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise Refusal(f"{path} does not exist") from error
    except OSError as error:
        raise Refusal(f"cannot read {path}: {error}") from error
    except tomllib.TOMLDecodeError as error:
        raise Refusal(f"{path} is not valid TOML: {error}") from error


def toolchain_channel(path: Path) -> str:
    toolchain = _read_toml(path).get("toolchain")
    channel = toolchain.get("channel") if isinstance(toolchain, dict) else None
    if not isinstance(channel, str):
        raise Refusal(f"{path} has no [toolchain] channel string")
    return channel


def declared_kani_corpus_rev(clone_rs: Path) -> str:
    try:
        text = clone_rs.read_text(encoding="utf-8")
    except OSError as error:
        raise Refusal(f"cannot read {clone_rs}: {error}") from error
    found = KANI_REV_DECLARATION.findall(text)
    if len(found) != 1:
        raise Refusal(
            f"{clone_rs} must declare `pub const DEFAULT_KANI_REV: &str = \"<rev>\";` "
            f"exactly once; found {len(found)}"
        )
    return found[0]


def pinned_kani_spec_rev(pins_path: Path, pin_name: str) -> str:
    """The `[revs.<pin_name>] rev` tools/kani-spec/pins.toml pins."""
    revs = _read_toml(pins_path).get("revs")
    body = revs.get(pin_name) if isinstance(revs, dict) else None
    rev = body.get("rev") if isinstance(body, dict) else None
    if not isinstance(rev, str) or REVISION.fullmatch(rev) is None or rev == "0" * 40:
        raise Refusal(
            f"{pins_path} must pin [revs.{pin_name}] rev as a nonzero 40-character "
            f"lowercase hex revision; found {rev!r}"
        )
    return rev


def spec_manifest_kani_rev(manifest: Path) -> str:
    """The `kani_rev` a generated spec/kani/<rev>/manifest.json records."""
    try:
        text = manifest.read_text(encoding="utf-8")
    except FileNotFoundError as error:
        raise Refusal(
            f"the generated spec manifest {manifest} does not exist; "
            "run tools/kani-spec/kani-spec generate and commit it"
        ) from error
    except OSError as error:
        raise Refusal(f"cannot read {manifest}: {error}") from error
    def unique_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        keys = [key for key, _ in pairs]
        duplicated = sorted({key for key in keys if keys.count(key) > 1})
        if duplicated:
            # json.loads keeps the last duplicate silently; an ambiguous
            # manifest must not pass on whichever copy happens to come last.
            raise Refusal(f"{manifest} repeats the key(s) {', '.join(duplicated)}")
        return dict(pairs)

    try:
        document = json.loads(text, object_pairs_hook=unique_keys)
    except json.JSONDecodeError as error:
        raise Refusal(f"{manifest} is not valid JSON: {error}") from error
    rev = document.get("kani_rev") if isinstance(document, dict) else None
    if not isinstance(rev, str):
        raise Refusal(f"{manifest} has no kani_rev string; found {rev!r}")
    return rev


def locked_git_commit(lock_path: Path, package: str, repository: str) -> str:
    packages = _read_toml(lock_path).get("package")
    if not isinstance(packages, list):
        raise Refusal(f"{lock_path} has no [[package]] list")
    entries = [
        entry
        for entry in packages
        if isinstance(entry, dict) and entry.get("name") == package
    ]
    if not entries:
        raise Refusal(f"{lock_path} has no {package} package")
    canonical = f"https://github.com/alabsystems/{repository}"
    commits: set[str] = set()
    for entry in entries:
        source = entry.get("source")
        version = entry.get("version")
        match = LOCK_GIT_SOURCE.fullmatch(source) if isinstance(source, str) else None
        if match is None:
            raise Refusal(
                f"{lock_path} resolves {package} {version} from {source!r}, "
                f"not an exact git revision of alabsystems/{repository}"
            )
        url = match["url"].removesuffix("/").removesuffix(".git")
        if url != canonical:
            raise Refusal(
                f"{lock_path} resolves {package} {version} from {match['url']}, "
                f"not {canonical}.git"
            )
        if match["rev"] != match["commit"]:
            raise Refusal(
                f"{lock_path} requests {package} rev {match['rev']} but locks "
                f"commit {match['commit']}"
            )
        commits.add(match["commit"])
    if len(commits) != 1:
        raise Refusal(f"{lock_path} resolves {package} at several commits: {sorted(commits)}")
    return commits.pop()


def parse_rustc_verbose(text: str) -> dict[str, str]:
    lines = text.splitlines()
    fields: dict[str, str] = {}
    if lines:
        fields["version"] = lines[0].strip()
    for line in lines[1:]:
        key, separator, value = line.partition(": ")
        if separator:
            fields[key.strip()] = value.strip()
    return fields


def trust_toolchain_override(environ: Mapping[str, str] | None = None) -> str | None:
    """The TRUST_MC_TRUST_TOOLCHAIN value the resolver sees, or None when unset.

    A set-but-empty value is returned as "" (the resolver refuses it), never
    folded into None, so a report cannot claim no override was in effect.
    """
    env = os.environ if environ is None else environ
    return env.get(TRUST_TOOLCHAIN_OVERRIDE_ENV)


def _override_clause(override: str | None) -> str:
    if override is None:
        return ""
    return f" with {TRUST_TOOLCHAIN_OVERRIDE_ENV}={override}"


@dataclass
class ToolchainProbe:
    override: str | None = None
    rustc: str | None = None
    verbose: dict[str, str] = field(default_factory=dict)
    rustc_error: str | None = None
    sysroot: str | None = None
    sysroot_error: str | None = None
    development_identity: dict[str, Any] | None = None


def probe_trust_toolchain(layout: Layout) -> ToolchainProbe:
    probe = ToolchainProbe(override=trust_toolchain_override())
    try:
        probe.rustc = _run([str(layout.resolver), "trustc"])
        probe.verbose = parse_rustc_verbose(_run([probe.rustc, "-Vv"]))
    except Refusal as error:
        probe.rustc_error = str(error)
    try:
        probe.sysroot = _run([str(layout.resolver), "sysroot"])
    except Refusal as error:
        probe.sysroot_error = str(error)
    return probe


# --- checks ---------------------------------------------------------------


def _guarded(
    check_id: str, expected: str, source: Path | str, body: Callable[[], Check]
) -> Check:
    try:
        return body()
    except Refusal as error:
        return Check(check_id, FAIL, expected, None, str(source), str(error))


def _compare(
    check_id: str, subject: str, expected: str, actual: str, source: Path | str
) -> Check:
    if actual == expected:
        return Check(check_id, PASS, expected, actual, str(source), f"{subject} is {actual}")
    return Check(
        check_id,
        FAIL,
        expected,
        actual,
        str(source),
        f"{subject} is {actual}, but the tuple names {expected}",
    )


def check_trust_channel(layout: Layout, tuple_: MeasurementTuple) -> Check:
    """rust-toolchain.toml's declared channel. An override does not change the
    declaration, only what resolves; trust.commit and trust.build judge that."""
    path = layout.repo_root / "rust-toolchain.toml"
    override = trust_toolchain_override()
    subject = "rust-toolchain.toml's channel"
    if override is not None:
        subject = (
            f"rust-toolchain.toml's channel (resolution overridden by "
            f"{TRUST_TOOLCHAIN_OVERRIDE_ENV}={override})"
        )
    return _guarded(
        "trust.channel",
        tuple_.trust_channel,
        path,
        lambda: _compare(
            "trust.channel",
            subject,
            tuple_.trust_channel,
            toolchain_channel(path),
            path,
        ),
    )


def check_trust_commit(probe: ToolchainProbe, tuple_: MeasurementTuple) -> Check:
    expected = tuple_.trust_rev
    via = _override_clause(probe.override)
    source = f"scripts/resolve-trust-tool.sh trustc{via}"
    if probe.rustc_error is not None:
        return Check(
            "trust.commit",
            FAIL,
            expected,
            None,
            source,
            f"cannot read the resolved Trust toolchain's commit-hash: {probe.rustc_error}",
        )
    commit = probe.verbose.get("commit-hash")
    if commit is None:
        return Check(
            "trust.commit",
            FAIL,
            expected,
            None,
            str(probe.rustc),
            f"`{probe.rustc} -Vv` reports no commit-hash line",
        )
    return _compare(
        "trust.commit",
        f"the commit-hash `{probe.rustc} -Vv` reports "
        f"(resolved by scripts/resolve-trust-tool.sh{via})",
        expected,
        commit,
        str(probe.rustc),
    )


def check_trust_build(probe: ToolchainProbe, tuple_: MeasurementTuple) -> Check:
    if tuple_.development_seal is not None:
        seal = tuple_.development_seal
        probe.development_identity = None
        expected = f"development:{tuple_.trust_rev}:{seal.provenance_sha256}"
        try:
            if probe.rustc_error is not None or probe.sysroot_error is not None:
                raise SealRefusal(f"resolved compiler/sysroot unavailable: {probe.rustc_error or probe.sysroot_error}")
            probe.development_identity = verify_development_seal(
                seal, tuple_.trust_rev,
                observed_sysroot=probe.sysroot, observed_compiler=probe.rustc,
                verbose=probe.verbose,
            )
        except SealRefusal as error:
            return Check("trust.build", FAIL, expected, probe.sysroot, seal.root, str(error))
        return Check(
            "trust.build", PASS, expected, expected, seal.root,
            "explicit development seal matches its compiler, Targo, driver and PROVENANCE; "
            + probe.development_identity["scope"],
        )
    expected = str(tuple_.trust_build)
    via = _override_clause(probe.override)
    if probe.sysroot_error is not None:
        return Check(
            "trust.build",
            FAIL,
            expected,
            None,
            f"scripts/resolve-trust-tool.sh sysroot{via}",
            f"cannot resolve the Trust toolchain's sysroot: {probe.sysroot_error}",
        )
    sysroot = str(probe.sysroot)
    build = Path(sysroot).name
    # An installed rollback build can physically live at
    # <prefix>/store/trust/<build>.noindex, with <build> only a compatibility
    # symlink. The resolver deliberately requires the physical prefix; do not
    # make callers use that alias or copy/rename an SDK just to recover its
    # selection number. Recognize only this exact native-store spelling and a
    # canonical real directory. This is build-selection metadata, never proof
    # authority: trust.commit and every remaining tuple check still apply.
    noindex_build = re.fullmatch(r"([1-9][0-9]*)\.noindex", build)
    if noindex_build is not None:
        root = Path(sysroot)
        try:
            physical_store = (
                root.parent.name == "trust"
                and root.parent.parent.name == "store"
                and root.is_dir()
                and root.resolve(strict=True) == root
            )
        except OSError:
            physical_store = False
        if physical_store:
            build = noindex_build.group(1)
    # The aterm package store names a seal by its build number (`.../trust/8595`).
    # A VAULTED seal is the same artifact under an archival name
    # (`.../trust-mc-seal-vault/seal-8595`), and vaulting is not optional: the
    # store keeps only the newest seals and pruned 8595 — the build every
    # measurement behind the current tuple was made on — within hours of
    # promoting past it. Refusing the vault spelling makes the tuple
    # unverifiable the moment the store rotates, which is exactly when it
    # matters most.
    #
    # Accept `seal-<digits>` as well as `<digits>`, and do NOT take the name's
    # word for it: a vault directory must also carry a PROVENANCE whose
    # `reported_commit` is the rev this tuple names, so a renamed directory
    # cannot claim a build it is not. (`trust.commit` independently compares
    # the compiler's own `-Vv` commit-hash; this is the second lock, not the
    # only one.)
    vaulted = False
    if not build.isdigit() and build.startswith("seal-") and build[5:].isdigit():
        provenance = _seal_provenance(sysroot) or {}
        reported = provenance.get("reported_commit")
        if reported is not None and reported == tuple_.trust_rev:
            build = build[5:]
            vaulted = True
        else:
            return Check(
                "trust.build",
                FAIL,
                expected,
                build,
                sysroot,
                f"the vaulted Trust sysroot {sysroot}{via} carries "
                + (
                    f"PROVENANCE reported_commit {reported}, not the {tuple_.trust_rev} "
                    "this tuple names"
                    if reported is not None
                    else "no PROVENANCE reported_commit, so its build cannot be confirmed"
                ),
            )
    if not build.isdigit():
        return Check(
            "trust.build",
            FAIL,
            expected,
            build,
            sysroot,
            f"the resolved Trust sysroot {sysroot}{via} is not a numbered seal "
            f"directory, so it cannot be confirmed as build {expected}",
        )
    return _compare(
        "trust.build",
        f"the seal build of the "
        f"{'VAULTED ' if vaulted else ''}resolved Trust sysroot {sysroot}{via}"
        + (", confirmed by its PROVENANCE reported_commit" if vaulted else ""),
        expected,
        build,
        sysroot,
    )


def check_frozen_channel(layout: Layout, tuple_: MeasurementTuple) -> Check:
    path = layout.repo_root / "rust-toolchain.legacy.toml"
    return _guarded(
        "frozen.channel",
        tuple_.frozen_channel,
        path,
        lambda: _compare(
            "frozen.channel",
            "rust-toolchain.legacy.toml's frozen Kani-lane channel",
            tuple_.frozen_channel,
            toolchain_channel(path),
            path,
        ),
    )


def _check_declared(
    check_id: str, label: str, audit_root: Path, family: str, expected: str, where: str
) -> Check:
    if not audit_root.is_dir():
        return Check(
            check_id,
            FAIL,
            expected,
            None,
            str(audit_root),
            f"{audit_root} does not exist, so its {label} declarations cannot be read",
        )
    try:
        audit = audit_repository(audit_root, family)
    except ValueError as error:
        findings = "; ".join(str(error).splitlines())
        return Check(
            check_id,
            FAIL,
            expected,
            None,
            str(audit_root),
            f"the {label} declarations in {where} are not one exact pin: {findings}",
        )
    return _compare(
        check_id,
        f"the {label} revision declared by {where} "
        f"({audit.declarations} declaration{'s' if audit.declarations != 1 else ''})",
        expected,
        audit.revision,
        audit_root,
    )


def check_ay_manifest(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_declared(
        "ay.manifest", "AY", layout.repo_root, "ay", tuple_.ay_rev, "Cargo.toml"
    )


def check_trust_ir_manifest(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_declared(
        "trust-ir.manifest",
        "TrustIR",
        layout.repo_root,
        "trust-ir",
        tuple_.trust_ir_rev,
        "trust-mc's manifests",
    )


def check_trust_vc_manifest(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_declared(
        "trust-vc.manifest",
        "trust-vc",
        layout.repo_root,
        "trust-vc",
        tuple_.trust_vc_rev,
        "trust-mc's manifests",
    )


def check_clean_manifest(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_declared(
        "clean.manifest",
        "Clean",
        layout.trust_ir_repo,
        "clean",
        tuple_.clean_rev,
        f"the manifests of the TrustIR checkout {layout.trust_ir_repo}",
    )


def _check_locked(
    check_id: str, layout: Layout, package: str, repository: str, expected: str
) -> Check:
    lock = layout.repo_root / "Cargo.lock"
    return _guarded(
        check_id,
        expected,
        lock,
        lambda: _compare(
            check_id,
            f"the {package} commit Cargo.lock resolves",
            expected,
            locked_git_commit(lock, package, repository),
            lock,
        ),
    )


def check_trust_vc_lock(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_locked(
        "trust-vc.lock", layout, "trust-vc-merge-contract", "trust-vc", tuple_.trust_vc_rev
    )


def check_clean_lock(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_locked("clean.lock", layout, "clean-kernel", "clean", tuple_.clean_rev)


def check_checkout(
    check_id: str,
    label: str,
    checkout: Path,
    expected: str,
    *,
    count_untracked: bool = True,
    absent_note: str | None = None,
) -> Check:
    """The checkout's HEAD must be the tuple revision, with no local changes.

    count_untracked=False ignores untracked files (run artifacts). absent_note,
    when given, reports a checkout that does not exist yet as unchecked instead
    of refusing it.
    """

    def body() -> Check:
        if absent_note is not None and not checkout.exists() and not checkout.is_symlink():
            return Check(
                check_id,
                UNCHECKED,
                expected,
                None,
                str(checkout),
                f"the {label} checkout {checkout} does not exist yet; {absent_note}",
            )
        if not checkout.is_dir():
            raise Refusal(f"the {label} checkout {checkout} does not exist")
        try:
            top = Path(_git(checkout, "rev-parse", "--show-toplevel")).resolve()
        except Refusal as error:
            raise Refusal(f"the {label} checkout {checkout} is not a git worktree: {error}") from error
        if top != checkout.resolve():
            raise Refusal(
                f"the {label} checkout {checkout} is inside git worktree {top}, "
                "not a checkout root"
            )
        head = _git(checkout, "rev-parse", "HEAD")
        if head != expected:
            return Check(
                check_id,
                FAIL,
                expected,
                head,
                str(checkout),
                f"the {label} checkout {checkout} HEAD is {head}, but the tuple names {expected}",
            )
        untracked = "normal" if count_untracked else "no"
        status = _git(checkout, "status", "--porcelain", f"--untracked-files={untracked}")
        if status:
            changed = status.splitlines()
            return Check(
                check_id,
                FAIL,
                expected,
                f"{head}-dirty",
                str(checkout),
                f"the {label} checkout {checkout} is at {head} but dirty: "
                f"{len(changed)} changed path(s), first `{changed[0].strip()}`",
            )
        return Check(
            check_id,
            PASS,
            expected,
            head,
            str(checkout),
            f"the {label} checkout {checkout} is clean at {head}",
        )

    return _guarded(check_id, expected, checkout, body)


def _check_kani_spec_pin(
    check_id: str, layout: Layout, pin_name: str, tuple_key: str, expected: str
) -> Check:
    """pins.toml's [revs.<pin_name>] rev is the tuple's rev, and the generated
    spec/kani/<rev>/manifest.json exists and records that same kani_rev.

    Fail-closed: an unreadable pins file or a missing or malformed manifest
    refuses the check rather than leaving it unchecked.
    """
    pins = layout.kani_spec_pins

    def body() -> Check:
        pinned = pinned_kani_spec_rev(pins, pin_name)
        if pinned != expected:
            return Check(
                check_id,
                FAIL,
                expected,
                pinned,
                str(pins),
                f"{pins} pins [revs.{pin_name}] rev = {pinned}, but the tuple's "
                f"[kani] {tuple_key} is {expected}",
            )
        manifest = layout.kani_spec_manifest(pinned)
        recorded = spec_manifest_kani_rev(manifest)
        if recorded != pinned:
            return Check(
                check_id,
                FAIL,
                expected,
                recorded,
                str(manifest),
                f"{manifest} records kani_rev {recorded}, but pins.toml [revs.{pin_name}] "
                f"and the tuple's [kani] {tuple_key} name {pinned}",
            )
        return Check(
            check_id,
            PASS,
            expected,
            recorded,
            str(manifest),
            f"pins.toml [revs.{pin_name}] rev and {manifest}'s kani_rev are both {recorded}",
        )

    return _guarded(check_id, expected, pins, body)


def check_kani_corpus(layout: Layout, tuple_: MeasurementTuple) -> Check:
    """DEFAULT_KANI_REV, pins.toml's [revs.corpus] and its generated manifest
    all name the tuple's corpus rev."""
    clone_rs = layout.repo_root / "tools" / "kani-domination" / "src" / "clone.rs"
    declared = _guarded(
        "kani.corpus",
        tuple_.kani_corpus_rev,
        clone_rs,
        lambda: _compare(
            "kani.corpus",
            "tools/kani-domination's DEFAULT_KANI_REV",
            tuple_.kani_corpus_rev,
            declared_kani_corpus_rev(clone_rs),
            clone_rs,
        ),
    )
    if declared.status != PASS:
        return declared
    pinned = _check_kani_spec_pin(
        "kani.corpus", layout, "corpus", "corpus_rev", tuple_.kani_corpus_rev
    )
    if pinned.status != PASS:
        return pinned
    return Check(
        "kani.corpus",
        PASS,
        tuple_.kani_corpus_rev,
        tuple_.kani_corpus_rev,
        str(clone_rs),
        f"{declared.message}; {pinned.message}",
    )


def check_kani_checkout(layout: Layout, tuple_: MeasurementTuple) -> Check:
    """The corpus checkout kani-domination actually reads is clean at the tuple rev.

    DEFAULT_KANI_REV is only the declaration: kani-domination reuses an existing
    checkout at whatever rev it holds, and when a by-SHA fetch is refused it
    clones Kani's default-branch HEAD with only a warning.
    """
    clone_rs = layout.repo_root / "tools" / "kani-domination" / "src" / "clone.rs"
    try:
        # The default checkout is keyed by the declared rev. When that
        # declaration is unreadable kani.corpus already refuses, so the tuple's
        # rev only locates the directory.
        try:
            rev = declared_kani_corpus_rev(clone_rs)
        except Refusal:
            rev = tuple_.kani_corpus_rev
        checkout = layout.kani_checkout(rev)
    except Refusal as error:
        return Check(
            "kani.checkout", FAIL, tuple_.kani_corpus_rev, None, KANI_CORPUS_DIR_ENV, str(error)
        )
    return check_checkout(
        "kani.checkout",
        "Kani corpus",
        checkout,
        tuple_.kani_corpus_rev,
        count_untracked=False,
        absent_note="tools/kani-domination clones it on its first run, so re-run "
        "tuple-check once it exists and before counting a row",
    )


def check_kani_spec(layout: Layout, tuple_: MeasurementTuple) -> Check:
    return _check_kani_spec_pin(
        "kani.spec", layout, "spec", "spec_rev", tuple_.kani_spec_rev
    )


def run_checks(layout: Layout, tuple_: MeasurementTuple) -> tuple[list[Check], ToolchainProbe]:
    probe = probe_trust_toolchain(layout)
    checks = [
        check_trust_channel(layout, tuple_),
        check_trust_commit(probe, tuple_),
        check_trust_build(probe, tuple_),
        check_frozen_channel(layout, tuple_),
        check_ay_manifest(layout, tuple_),
        check_checkout("ay.checkout", "AY", layout.ay_repo, tuple_.ay_rev),
        check_trust_ir_manifest(layout, tuple_),
        check_checkout("trust-ir.checkout", "TrustIR", layout.trust_ir_repo, tuple_.trust_ir_rev),
        check_trust_vc_manifest(layout, tuple_),
        check_trust_vc_lock(layout, tuple_),
        check_clean_manifest(layout, tuple_),
        check_clean_lock(layout, tuple_),
        check_kani_corpus(layout, tuple_),
        check_kani_checkout(layout, tuple_),
        check_kani_spec(layout, tuple_),
    ]
    assert tuple(check.id for check in checks) == CHECK_IDS
    return checks, probe


# --- report ---------------------------------------------------------------


def _seal_provenance(sysroot: str | None) -> dict[str, str] | None:
    if sysroot is None:
        return None
    path = Path(sysroot) / "PROVENANCE"
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return None
    wanted = {
        "provenance_class",
        "seal_name",
        "sealed_at",
        "reported_commit",
        "artifact_driver_sha256",
    }
    fields: dict[str, str] = {}
    for line in text.splitlines():
        key, separator, value = line.partition("=")
        if separator and key in wanted:
            fields[key] = value
    return fields


def _trust_mc_state(repo_root: Path) -> dict[str, Any]:
    try:
        head: str | None = _git(repo_root, "rev-parse", "HEAD")
        dirty: bool | None = bool(
            _git(repo_root, "status", "--porcelain", "--untracked-files=normal")
        )
    except Refusal:
        head, dirty = None, None
    return {"root": str(repo_root), "head": head, "dirty": dirty}


def evaluate(repo_root: Path, tuple_path: Path, *, allow_development: bool = True) -> dict[str, Any]:
    """Load and check the tuple; raise TupleError if the tuple is malformed."""
    tuple_ = load_tuple(tuple_path)
    if tuple_.development_seal is not None and not allow_development:
        raise TupleError(f"{tuple_path}: schema 2 development identity requires explicit --tuple selection")
    layout = Layout(repo_root)
    checks, probe = run_checks(layout, tuple_)
    failed = [check.id for check in checks if check.status == FAIL]
    report = {
        "schema": REPORT_SCHEMA,
        "ok": not failed,
        "tuple_path": str(tuple_path),
        "tuple_sha256": tuple_.source_sha256,
        "tuple": tuple_.document,
        "checks": [asdict(check) for check in checks],
        "failed": failed,
        "unchecked": [check.id for check in checks if check.status == UNCHECKED],
        "trust": {"toolchain_override": probe.override},
        "observed": {
            "trust_mc": _trust_mc_state(repo_root),
            "trust_toolchain": {
                "rustc": probe.rustc,
                "version": probe.verbose.get("version"),
                "commit_date": probe.verbose.get("commit-date"),
                "trust": probe.verbose.get("trust"),
                "sysroot": probe.sysroot,
                # The development authority reader is bounded and no-follow;
                # do not re-read its provenance through the legacy diagnostic path.
                "seal_provenance": (
                    None if tuple_.development_seal is not None else _seal_provenance(probe.sysroot)
                ),
            },
        },
    }
    if tuple_.development_seal is not None:
        report["schema"] = DEVELOPMENT_TUPLE_SCHEMA
        report["trust"].update({
            "identity_classification": "development",
            "identity_scope": (
                probe.development_identity["scope"] if probe.development_identity is not None else IDENTITY_SCOPE
            ),
            "development_identity_established": next(
                check.status == PASS for check in checks if check.id == "trust.build"
            ),
            "development_identity": probe.development_identity,
        })
    return report


def _print_text(report: dict[str, Any]) -> None:
    if report["trust"].get("identity_classification") == "development":
        print(f"tuple-check: note: explicit development tuple; {report['trust']['identity_scope']}")
    override = report["trust"]["toolchain_override"]
    if override is not None:
        print(
            f"tuple-check: note: {TRUST_TOOLCHAIN_OVERRIDE_ENV}={override} selects the "
            "Trust toolchain in place of rust-toolchain.toml's channel"
        )
    for check in report["checks"]:
        if check["status"] == FAIL:
            print(f"tuple-check: error: {check['id']}: {check['message']}", file=sys.stderr)
        elif check["status"] == UNCHECKED:
            print(f"tuple-check: note: {check['id']}: {check['message']}")
        else:
            print(f"tuple-check: ok: {check['id']}: {check['message']}")
    total = len(report["checks"])
    if report["ok"]:
        checked = total - len(report["unchecked"])
        print(
            f"tuple-check: ok: {report['tuple_path']} matches this host "
            f"({checked} checks pass, {len(report['unchecked'])} unchecked)"
        )
    else:
        print(
            f"tuple-check: error: {len(report['failed'])} of {total} checks refuse "
            f"{report['tuple_path']}: {', '.join(report['failed'])}",
            file=sys.stderr,
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="tuple-check",
        description="Check tools/tuple.toml against this workspace, its sibling "
        "checkouts and the resolved Trust toolchain. Exit 0 on a match, 1 on any "
        "mismatch, 2 when the tuple itself is unreadable or malformed.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="trust-mc checkout to check (siblings are its ../ay and ../trust-ir)",
    )
    parser.add_argument(
        "--tuple", type=Path, default=None, help="tuple file (default: <repo-root>/tools/tuple.toml)"
    )
    parser.add_argument(
        "--json", action="store_true", help="print the report as JSON on stdout"
    )
    args = parser.parse_args(argv)
    repo_root = args.repo_root.resolve()
    tuple_path = (args.tuple or repo_root / "tools" / "tuple.toml").resolve()

    try:
        report = evaluate(repo_root, tuple_path, allow_development=args.tuple is not None)
    except TupleError as error:
        if args.json:
            print(
                json.dumps(
                    {
                        "schema": REPORT_SCHEMA,
                        "ok": False,
                        "tuple_path": str(tuple_path),
                        "error": str(error),
                    },
                    indent=2,
                )
            )
        for line in str(error).splitlines():
            print(f"tuple-check: error: {line}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(report, indent=2))
        for check in report["checks"]:
            if check["status"] == FAIL:
                print(
                    f"tuple-check: error: {check['id']}: {check['message']}",
                    file=sys.stderr,
                )
    else:
        _print_text(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
