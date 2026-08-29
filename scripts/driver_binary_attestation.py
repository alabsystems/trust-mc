#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Attest the exact TrustMC driver that produced replacement evidence."""

from __future__ import annotations

import hashlib
import os
import re
import subprocess
from pathlib import Path
from typing import Any


AUTHORITY_PREFIX = "trust_mc-version-authority"
FULL_SHA_RE = re.compile(r"[0-9a-f]{40}")
SHA256_RE = re.compile(r"[0-9a-f]{64}")
REQUIRED_AUTHORITY_FIELDS = frozenset(
    {
        "version",
        "invocation",
        "trust_mc_sha",
        "trust_mc_dirty",
        "ay_version",
        "ay_pin",
        "ay_linked_sha",
        "ay_linked_dirty",
        "ay_authority",
    }
)


class DriverAttestationError(ValueError):
    """The driver cannot provide current, clean version authority."""


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            while chunk := handle.read(1024 * 1024):
                digest.update(chunk)
    except OSError as err:
        raise DriverAttestationError(f"unable to hash driver {path}: {err}") from err
    return digest.hexdigest()


def parse_authority_output(output: str) -> dict[str, str]:
    """Parse the driver's single machine-readable authority line."""

    nonempty = [line.strip() for line in output.splitlines() if line.strip()]
    if len(nonempty) != 1 or not nonempty[0].startswith(f"{AUTHORITY_PREFIX} "):
        raise DriverAttestationError(
            "driver --version-authority must emit exactly one authority line"
        )

    fields: dict[str, str] = {}
    for token in nonempty[0].split()[1:]:
        key, separator, value = token.partition("=")
        if not separator or not key or not value:
            raise DriverAttestationError(
                f"malformed driver authority token {token!r}"
            )
        if key in fields:
            raise DriverAttestationError(
                f"duplicate driver authority field {key!r}"
            )
        fields[key] = value

    missing = REQUIRED_AUTHORITY_FIELDS - fields.keys()
    unknown = fields.keys() - REQUIRED_AUTHORITY_FIELDS
    if missing or unknown:
        details = []
        if missing:
            details.append(f"missing={sorted(missing)!r}")
        if unknown:
            details.append(f"unknown={sorted(unknown)!r}")
        raise DriverAttestationError(
            "invalid driver authority fields: " + " ".join(details)
        )
    return fields


def validate_attestation(
    attestation: Any,
    *,
    expected_trust_mc_sha: str,
    expected_ay_pin: str,
) -> list[str]:
    """Return every structural or authority failure in a report attestation."""

    if not isinstance(attestation, dict):
        return ["driver_binary attestation is missing or not an object"]

    failures: list[str] = []
    if attestation.get("name") != "trust-mc-driver":
        failures.append(
            f"driver_binary.name {attestation.get('name')!r} != 'trust-mc-driver'"
        )

    path = attestation.get("path")
    if not isinstance(path, str) or not path.strip():
        failures.append("driver_binary.path is missing or empty")
    elif not Path(path).is_absolute():
        failures.append(f"driver_binary.path {path!r} is not absolute")

    digest = attestation.get("sha256")
    if not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None:
        failures.append(
            f"driver_binary.sha256 {digest!r} is not a lowercase SHA-256 digest"
        )

    for field in ("version", "ay_version"):
        value = attestation.get(field)
        if not isinstance(value, str) or not value:
            failures.append(f"driver_binary.{field} is missing or empty")

    if attestation.get("invocation") != "standalone":
        failures.append(
            f"driver_binary.invocation {attestation.get('invocation')!r} "
            "!= 'standalone'"
        )

    trust_mc_sha = attestation.get("trust_mc_sha")
    if trust_mc_sha != expected_trust_mc_sha:
        failures.append(
            f"driver_binary.trust_mc_sha {trust_mc_sha!r} "
            f"!= expected {expected_trust_mc_sha!r}"
        )
    if attestation.get("trust_mc_dirty") is not False:
        failures.append(
            f"driver_binary.trust_mc_dirty {attestation.get('trust_mc_dirty')!r} "
            "is not false"
        )

    ay_pin = attestation.get("ay_pin")
    if ay_pin != expected_ay_pin:
        failures.append(
            f"driver_binary.ay_pin {ay_pin!r} != expected {expected_ay_pin!r}"
        )
    linked_sha = attestation.get("ay_linked_sha")
    if not isinstance(linked_sha, str) or FULL_SHA_RE.fullmatch(linked_sha) is None:
        failures.append(
            f"driver_binary.ay_linked_sha {linked_sha!r} is not a lowercase full SHA"
        )
    if attestation.get("ay_linked_dirty") is not False:
        failures.append(
            f"driver_binary.ay_linked_dirty {attestation.get('ay_linked_dirty')!r} "
            "is not false"
        )

    authority = attestation.get("ay_authority")
    if authority not in {"matched", "contains-pin"}:
        failures.append(
            f"driver_binary.ay_authority {authority!r} is not an accepted authority"
        )
    elif authority == "matched" and linked_sha != expected_ay_pin:
        failures.append(
            "driver_binary matched authority does not link the exact expected AY pin"
        )
    return failures


def attest_driver_binary(
    driver: Path,
    *,
    expected_trust_mc_sha: str,
    expected_ay_pin: str,
) -> dict[str, Any]:
    """Run ``--version-authority`` and bind the report to the executable bytes."""

    driver = driver.resolve()
    if not driver.is_file() or not os.access(driver, os.X_OK):
        raise DriverAttestationError(f"driver is not executable: {driver}")
    try:
        result = subprocess.run(
            [str(driver), "--version-authority"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as err:
        raise DriverAttestationError(
            f"unable to attest {driver} --version-authority: {err}"
        ) from err
    if result.returncode != 0:
        raise DriverAttestationError(
            f"{driver} --version-authority exited {result.returncode}: "
            f"{result.stdout.strip()}"
        )
    fields = parse_authority_output(result.stdout)
    for field in ("trust_mc_dirty", "ay_linked_dirty"):
        if fields[field] not in {"0", "1"}:
            raise DriverAttestationError(
                f"driver authority {field} must be 0 or 1, got {fields[field]!r}"
            )
    for field in ("trust_mc_sha", "ay_pin", "ay_linked_sha"):
        if FULL_SHA_RE.fullmatch(fields[field]) is None:
            raise DriverAttestationError(
                f"driver authority {field} is not a lowercase full SHA"
            )
    attestation: dict[str, Any] = {
        "name": "trust-mc-driver",
        "path": str(driver),
        "sha256": _sha256_file(driver),
        "version": fields["version"],
        "invocation": fields["invocation"],
        "trust_mc_sha": fields["trust_mc_sha"].lower(),
        "trust_mc_dirty": fields["trust_mc_dirty"] == "1",
        "ay_version": fields["ay_version"],
        "ay_pin": fields["ay_pin"].lower(),
        "ay_linked_sha": fields["ay_linked_sha"].lower(),
        "ay_linked_dirty": fields["ay_linked_dirty"] == "1",
        "ay_authority": fields["ay_authority"],
    }
    failures = validate_attestation(
        attestation,
        expected_trust_mc_sha=expected_trust_mc_sha,
        expected_ay_pin=expected_ay_pin,
    )
    if failures:
        raise DriverAttestationError("; ".join(failures))
    return attestation


def find_workspace_driver(repo_root: Path) -> Path:
    """Resolve the same first driver candidate used by ``scripts/trust-mc``."""

    candidates = [repo_root / "target/trust-mc/bin/trust-mc-driver"]
    cargo_target = os.environ.get("CARGO_TARGET_DIR")
    if cargo_target:
        candidates.append(repo_root / cargo_target / "release/trust-mc-driver")
    candidates.extend(
        (
            repo_root / "target/release/trust-mc-driver",
            repo_root / "target/debug/trust-mc-driver",
        )
    )
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate.resolve()
    rendered = ", ".join(str(path) for path in candidates)
    raise DriverAttestationError(f"no executable workspace driver found in: {rendered}")
