#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Compiler identity and local build receipts for the unverified pinned AY CLI."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile

import ay_cli_build_policy

SCHEMA = "trust-mc.ay-cli-build/v2"
PROTOCOL = "trust-mc.ay-compiler-bound/v1"


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()



def driver_identity(root: Path) -> dict:
    """Match the keyed-builder's PROVENANCE identity and bind installed bytes."""
    fields = {}
    provenance = root / "PROVENANCE"
    if provenance.is_file():
        for line in provenance.read_text().splitlines():
            key, separator, value = line.partition("=")
            key = key.strip()
            if separator and key in ("artifact_driver_sha256", "artifact_driver_name"):
                if key in fields:
                    raise ValueError(f"PROVENANCE repeats {key}")
                fields[key] = value.strip()
    name = fields.get("artifact_driver_name")
    if name:
        if Path(name).name != name:
            raise ValueError("PROVENANCE driver name is not a filename")
        driver = root / "lib" / name
        if not driver.is_file():
            raise ValueError("PROVENANCE driver is not installed")
    else:
        drivers = sorted(p for p in (root / "lib").glob("*rustc_driver-*") if p.is_file())
        if len(drivers) != 1:
            raise ValueError("the installed compiler driver is missing or ambiguous")
        driver = drivers[0]
    installed = digest(driver)
    recorded = fields.get("artifact_driver_sha256", installed)
    if not re.fullmatch(r"[0-9a-f]{64}", recorded):
        raise ValueError("PROVENANCE driver digest is not a lowercase sha256")
    return {
        "artifact_driver_sha256": recorded,
        "installed_driver_sha256": installed,
        "artifact_driver_name": driver.name,
    }

def compiler_identity(sysroot: str, trustc: str, targo: str, expected_targo: str) -> dict:
    """The compiler a build runs, as `toolchain` (what landing-gate.py keys its
    reuse on and an AY build is bound to) beside the resolved `trustc`, `targo`
    and `trustc -vV`. It reads no AY source: the gate has none to name."""
    root = str(Path(sysroot).resolve())
    compiler, frontend = Path(trustc).absolute(), Path(targo).resolve()
    if frontend != Path(expected_targo).resolve():
        raise ValueError("TRUST_MC_TARGO does not name the pinned compiler's targo")
    version = subprocess.run(
        [str(compiler), "-vV"], check=True, capture_output=True, text=True
    ).stdout
    reported = subprocess.run(
        [str(compiler), "--print", "sysroot"], check=True, capture_output=True, text=True
    ).stdout.strip()
    if str(Path(reported).resolve()) != root:
        raise ValueError("the resolved trustc reports a different sysroot")
    # Shared with landing-gate.py: the launcher alone is not the compiler.
    toolchain = {
        "sysroot": root,
        "trustc_vV_sha256": hashlib.sha256(version.encode()).hexdigest(),
        "trustc_sha256": digest(compiler),
        "targo_sha256": digest(frontend),
        **driver_identity(Path(root)),
    }
    return {"toolchain": toolchain, "trustc": str(compiler), "targo": str(frontend), "trustc_vV": version}


def identify(sysroot: str, trustc: str, targo: str, expected_targo: str, source: str, pin: str) -> dict:
    """The identity an AY build at `pin` from `source` is keyed by: the
    compiler (`compiler_identity`) and the AY source's build policy."""
    compiler = compiler_identity(sysroot, trustc, targo, expected_targo)
    identity = {"toolchain": compiler["toolchain"],
                "build_policy": ay_cli_build_policy.source_policy(Path(source), pin, compiler["trustc_vV"])}
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    return {
        "key": key,
        "identity": identity,
        "trustc": compiler["trustc"],
        "targo": compiler["targo"],
        "trustc_vV": compiler["trustc_vV"],
    }


def matches(receipt: Path, binary: Path, pin: str, builder: dict) -> bool:
    try:
        record = json.loads(receipt.read_text())
        return (
            record["schema"] == SCHEMA
            and record["ay_commit"] == pin
            and record["builder"] == builder
            and record["binary_sha256"] == digest(binary)
        )
    except (OSError, ValueError, KeyError, TypeError):
        return False


def record(receipt: Path, binary: Path, pin: str, builder: dict) -> None:
    data = {
        "schema": SCHEMA,
        "lane": "unverified",
        "ay_commit": pin,
        "builder": builder,
        "binary_sha256": digest(binary),
    }
    with tempfile.NamedTemporaryFile(mode="w", dir=receipt.parent, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(data, stream, sort_keys=True, indent=2)
        stream.write("\n")
    try:
        os.replace(temporary, receipt)
    finally:
        temporary.unlink(missing_ok=True)


def stage_bundle(binary: Path, destination: Path, pin: str, builder: dict, compiler_commit: str) -> None:
    """Copy a checked source/compiler-bound helper into a fresh release closure.

    The portable origin record describes pre-relocation bytes. The canonical
    package's signed whole-tree root authenticates the final installed bytes.
    """
    if not re.fullmatch(r"[0-9a-f]{40}", pin) or not re.fullmatch(r"[0-9a-f]{40}", compiler_commit):
        raise ValueError("bundle source/compiler identity must be full lowercase commits")
    if not re.search(r"^commit-hash: " + compiler_commit + r"$", builder["trustc_vV"], re.MULTILINE):
        raise ValueError("AY helper compiler differs from the admitted release compiler")
    receipt = binary.parent.parent / "builder.json"
    if binary.name not in ("ay", "ay.exe") or binary.is_symlink() or not binary.is_file() or not os.access(binary, os.X_OK):
        raise ValueError("bundled AY input must be a regular executable")
    if receipt.is_symlink() or not matches(receipt, binary, pin, builder):
        raise ValueError("bundled AY lacks the exact source/compiler/binary build receipt")
    version = subprocess.run([str(binary), "--version"], check=True, capture_output=True, text=True).stdout
    if not re.search(r"\+build\.[0-9]+\." + pin + r"(?:@|\s|$)", version):
        raise ValueError("bundled AY is dirty, off-pin or unstamped")
    source = binary.parent.parent / "src"
    def source_git(*args):
        return subprocess.run(["git", "--no-optional-locks", "-C", str(source), *args],
                              check=True, capture_output=True, text=True).stdout.strip()
    if source_git("rev-parse", "HEAD") != pin or source_git("status", "--porcelain", "--untracked-files=normal"):
        raise ValueError("bundled AY license source is not the clean exact pinned checkout")
    names = source_git("ls-tree", "--name-only", pin).splitlines()
    licenses = [source / name for name in names if name.startswith("LICENSE") or name in ("NOTICE", "COPYRIGHT")]
    if not licenses or any(p.is_symlink() or not p.is_file() for p in licenses):
        raise ValueError("bundled AY requires regular pinned license/notice files")
    for license_file in licenses:
        expected = subprocess.run(["git", "--no-optional-locks", "-C", str(source), "show", f"{pin}:{license_file.name}"],
                                  check=True, capture_output=True).stdout
        if license_file.read_bytes() != expected:
            raise ValueError("bundled AY license differs from the pinned source blob")
    target = destination / "libexec"
    target.mkdir()
    installed = target / binary.name
    shutil.copy2(binary, installed, follow_symlinks=False)
    original = json.loads(receipt.read_text())
    if digest(installed) != original["binary_sha256"] or not matches(receipt, binary, pin, builder):
        raise ValueError("bundled AY changed during copying")
    license_dir = target / "ay-licenses"
    license_dir.mkdir()
    for license_file in licenses:
        shutil.copy2(license_file, license_dir / license_file.name, follow_symlinks=False)
    toolchain = builder["identity"]["toolchain"]
    portable = {"schema": "trust-mc.bundled-ay-origin/v1", "lane": "unverified",
                "ay_commit": pin, "compiler_commit": compiler_commit, "builder_key": builder["key"],
                "compiler_identity": {key: value for key, value in toolchain.items() if key != "sysroot"},
                "build_policy": builder["identity"]["build_policy"],
                "configuration": builder["configuration"],
                "build_binary_sha256": original["binary_sha256"],
                "hash_scope": "Compiler-bound input bytes before canonical package relocation/signing",
                "licenses": {p.name: digest(p) for p in licenses}}
    (target / "ay-origin.json").write_text(json.dumps(portable, sort_keys=True, indent=2) + "\n")


def main() -> int:
    try:
        command, *args = sys.argv[1:]
        if command == "identify":
            print(json.dumps(identify(*args), sort_keys=True))
        elif command == "configure":
            builder, lane, source = args
            print(json.dumps(ay_cli_build_policy.configure(json.loads(builder), Path(lane), Path(source)), sort_keys=True))
        elif command == "build":
            builder, lane, source, cache = args
            return ay_cli_build_policy.build(json.loads(builder), Path(lane), Path(source), Path(cache))
        elif command == "key":
            print(json.loads(args[0])["key"])
        elif command in ("matches", "record"):
            receipt, binary, pin, builder = args
            values = (Path(receipt), Path(binary), pin, json.loads(builder))
            if command == "matches":
                return 0 if matches(*values) else 1
            record(*values)
        elif command == "stage-bundle":
            binary, destination, pin, sysroot, trustc, targo, compiler_commit = args
            cache = Path(binary).parent.parent
            builder = identify(sysroot, trustc, targo, str(Path(sysroot) / "bin/targo"), str(cache / "src"), pin)
            builder = ay_cli_build_policy.configure(builder, cache / "lane", cache / "src")
            stage_bundle(Path(binary), Path(destination), pin, builder, compiler_commit)
        else:
            raise ValueError("unknown identity command")
        return 0
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        print(f"ay-cli-build-identity: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
