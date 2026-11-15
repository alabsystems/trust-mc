#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Portable native CPU policy for the compiler-bound private AY helper.

Cargo's resolved configuration stays in memory. Receipts contain only the
relevant configuration digest, never the complete configuration or diagnostics.
The query and build use exactly the same working directory and environment.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

import ay_cli_lane_config

SCHEMA = "trust-mc.ay-cli-policy/v1"
CPUS = {
    "aarch64-apple-darwin": "apple-m1",
    "aarch64-unknown-linux-gnu": "generic",
    "aarch64-unknown-linux-musl": "generic",
    "x86_64-apple-darwin": "x86-64-v2",
    "x86_64-unknown-linux-gnu": "x86-64-v2",
    "x86_64-unknown-linux-musl": "x86-64-v2",
}
REMOVED_ENV = {
    "RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_RUSTDOCFLAGS", "CARGO_BUILD_TARGET",
    "TRUSTFLAGS", "CARGO_ENCODED_TRUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN",
    "CARGO_TARGET_DIR", "TRUST_STAGE2_BIN",
}


def sha(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_policy(source: Path, pin: str, version: str) -> dict:
    hosts = re.findall(r"^host: ([^\s]+)$", version, re.MULTILINE)
    if len(hosts) != 1 or hosts[0] not in CPUS:
        raise ValueError("AY helper compiler has no single supported native CPU policy")
    host = hosts[0]
    # Read the admitted Git object, not a possibly modified checkout config.
    tree = subprocess.run(["git", "-C", str(source), "rev-parse", f"{pin}^{{commit}}"],
                          capture_output=True, text=True)
    if tree.returncode or tree.stdout.strip() != pin:
        raise ValueError("AY pin is unavailable locally; admit its exact source through native agh")
    entry = subprocess.run(["git", "-C", str(source), "ls-tree", pin, "--", ".cargo/config.toml"],
                           check=True, capture_output=True, text=True).stdout
    if entry:
        if not entry.startswith("100644 blob "):
            raise ValueError("AY source config must be a regular pinned Git blob")
        data = subprocess.run(["git", "-C", str(source), "show", f"{pin}:.cargo/config.toml"],
                              check=True, capture_output=True).stdout
    else:
        data = b""
    return {"schema": SCHEMA, "host": host, "target_cpu": CPUS[host],
            "source_config_sha256": sha(data),
            "recipe_sha256": sha(Path(__file__).read_bytes()),
            "lane_recipe_sha256": sha(Path(ay_cli_lane_config.__file__).read_bytes())}


def environment(builder: dict) -> dict:
    host = builder["identity"]["build_policy"]["host"].replace("-", "_").upper()
    removed = REMOVED_ENV | {f"CARGO_{group}_{host}_{flags}"
                             for group in ("TARGET", "HOST")
                             for flags in ("RUSTFLAGS", "RUSTDOCFLAGS")}
    removed |= {"CARGO_HOST_RUSTFLAGS", "CARGO_HOST_RUSTDOCFLAGS"}
    env = {key: value for key, value in os.environ.items() if key not in removed}
    env["RUSTC"] = env["CARGO_BUILD_RUSTC"] = builder["trustc"]
    env["PATH"] = str(Path(builder["targo"]).parent) + os.pathsep + env.get("PATH", "")
    return env


def flags_nonempty(value) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return bool(value)
    raise ValueError("AY helper Cargo rustflags must be strings or string arrays")


def suffix(key: str, original, cpu: str) -> list[str]:
    if original is not None:
        flags_nonempty(original)
    value = f"{original} -C target-cpu={cpu}" if isinstance(original, str) else ["-C", f"target-cpu={cpu}"]
    return ["--config", key + "=" + json.dumps(value)]


def floor_args(config: dict, host: str, cpu: str) -> list[str]:
    if not isinstance(config, dict):
        raise ValueError("AY helper Cargo configuration is not a table")
    build, targets, hosts = (config.get(name, {}) for name in ("build", "target", "host"))
    if not all(isinstance(value, dict) for value in (build, targets, hosts)):
        raise ValueError("AY helper Cargo policy has malformed tables")
    # Even an explicit native --target changes Cargo host/fallback selection and
    # output layout. The canonical helper always uses native config discovery.
    if "target" in build:
        raise ValueError("AY helper build.target routing is forbidden for the native bundle")
    if any(build.get(key) for key in ("rustc-wrapper", "rustc-workspace-wrapper")):
        raise ValueError("AY helper Cargo compiler wrappers are forbidden")
    configured_env = config.get("env", {})
    if not isinstance(configured_env, dict):
        raise ValueError("AY helper Cargo env is not a table")
    forbidden_env = REMOVED_ENV | {"RUSTC", "CARGO_BUILD_RUSTC", "CARGO_HOST_RUSTFLAGS", "CARGO_HOST_RUSTDOCFLAGS"}
    if any(key in forbidden_env or
           (key.startswith(("CARGO_TARGET_", "CARGO_HOST_")) and key.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS")))
           for key in configured_env):
        raise ValueError("AY helper Cargo env replaces compiler policy or routing")
    args = []
    for target, table in sorted(targets.items()):
        if not isinstance(table, dict):
            raise ValueError("AY helper target policy is not a table")
        flags = table.get("rustflags")
        if flags is not None and flags_nonempty(flags):
            # Making an empty target segment nonempty would hide build fallback.
            args += suffix("target." + json.dumps(target) + ".rustflags", flags, cpu)
    args += suffix("build.rustflags", build.get("rustflags"), cpu)
    if host in hosts:
        if not isinstance(hosts[host], dict):
            raise ValueError("AY helper host policy is not a table")
        key, flags = "host." + json.dumps(host) + ".rustflags", hosts[host].get("rustflags")
    else:
        # Cargo selects a specific host table as a whole, including linker-only
        # tables. Never invent one and shadow the declared default host policy.
        key, flags = "host.rustflags", hosts.get("rustflags")
    return args + suffix(key, flags, cpu)


def resolve(builder: dict, lane: Path, source: Path) -> tuple[dict, list[str]]:
    policy = builder["identity"]["build_policy"]
    source_config = source / ".cargo/config.toml"
    data = source_config.read_bytes() if source_config.is_file() else b""
    text = data.decode("utf-8")
    if sha(data) != policy["source_config_sha256"]:
        raise ValueError("AY helper source configuration differs from its pinned policy")
    expected = ay_cli_lane_config.derive(text, source.resolve())
    actual = (lane / ".cargo/config.toml").read_text()
    if ay_cli_lane_config.toml_loads(expected) != ay_cli_lane_config.toml_loads(actual):
        raise ValueError("AY helper lane configuration differs from the pinned derivation")
    query = subprocess.run([builder["targo"], "-Z", "unstable-options", "config", "get", "--format", "json"],
                           cwd=lane, env=environment(builder), capture_output=True)
    if query.returncode:
        # Cargo may print unrelated credential values when configuration fails.
        raise ValueError(f"AY helper Cargo policy query failed (exit {query.returncode})")
    try:
        config = json.loads(query.stdout)
    except (ValueError, UnicodeError):
        raise ValueError("AY helper Cargo policy query returned malformed JSON") from None
    args = floor_args(config, policy["host"], policy["target_cpu"])
    # Do not retain registries/http/credential configuration. Configured env can
    # influence native build scripts; bind its digest without exposing its text.
    relevant = {key: config[key] for key in ("build", "target", "host", "profile", "unstable", "env",
                                            "target-applies-to-host") if key in config}
    binding = {"schema": SCHEMA, "derived_config_sha256": sha(canonical(ay_cli_lane_config.toml_loads(actual))),
               "effective_config_sha256": sha(canonical(relevant))}
    return binding, args


def configure(builder: dict, lane: Path, source: Path) -> dict:
    return {**builder, "configuration": resolve(builder, lane, source)[0]}


def build(builder: dict, lane: Path, source: Path, cache: Path) -> int:
    binding, args = resolve(builder, lane, source)
    if binding != builder.get("configuration"):
        raise ValueError("AY helper Cargo policy changed before compilation")
    command = [builder["targo"], "--unverified", "build", "--locked", "--release", "-p", "ay", "--features", "cli",
               "--manifest-path", str(source / "Cargo.toml"), "--target-dir", str(cache), *args]
    return subprocess.run(command, cwd=lane, env=environment(builder)).returncode
