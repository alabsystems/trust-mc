# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Mirror of Kani compiletest collection (tools/compiletest/src/main.rs).

* rs modes (kani, kani-fixme, expected, coverage-based, stub-tests): every
  `*.rs` whose name does not start with `.`, `#` or `~`, recursing into every
  directory except `auxiliary`.
* cargo modes (cargo-kani, cargo-kani-test, cargo-coverage): in a directory
  that has `Cargo.toml`, every entry named `expected` or ending in
  `.expected` is a unit; every directory is recursed.
* exec: every entry directly under the suite directory is a unit and must
  carry `config.yml` (upstream aborts collection otherwise).

The suite/mode table is parsed from the rev's own CI scripts.
"""
from __future__ import annotations

import hashlib
import re
import tomllib

from . import SpecError
from .fsview import Tree
from .header import parse_props, test_description
from .rustscan import cfg_active, scan

RS_MODES = ("kani", "kani-fixme", "expected", "coverage-based", "stub-tests")
CARGO_MODES = ("cargo-kani", "cargo-kani-test", "cargo-coverage")
EXEC_MODES = ("exec",)
ALL_MODES = RS_MODES + CARGO_MODES + EXEC_MODES

REGRESSION = "scripts/kani-regression.sh"
EXTRA_SCRIPTS = ("scripts/kani-slow-tests.sh", "scripts/kani-perf.sh", "scripts/kani-llbc-regression.sh")
SCRIPT_JOBS = {
    "scripts/kani-regression.sh": ".github/workflows/kani.yml regression; .github/workflows/cbmc-latest.yml",
    "scripts/kani-slow-tests.sh": ".github/workflows/slow-tests.yml",
    "scripts/kani-perf.sh": ".github/workflows/kani.yml perf; .github/workflows/cbmc-latest.yml; .github/workflows/bench-e2e.yml",
    "scripts/kani-llbc-regression.sh": ".github/workflows/kani.yml llbc-regression",
}


def suite_table(tree: Tree) -> list:
    rows = []

    def add(suite, mode, script):
        if mode not in ALL_MODES:
            raise SpecError(f"{script}: unknown compiletest mode {mode!r} for suite {suite!r}")
        for r in rows:
            if r["suite"] == suite:
                if r["mode"] != mode:
                    raise SpecError(f"suite {suite} runs in two modes ({r['mode']}, {mode}); unit ids would collide")
                if script not in r["sources"]:
                    r["sources"].append(script)
                return
        rows.append({"suite": suite, "mode": mode, "sources": [script],
                     "ci_jobs": SCRIPT_JOBS.get(script, ""),
                     "perf_overlays": False})

    src = tree.read_text(REGRESSION)
    m = re.search(r"^TESTS=\((.*?)^\)", src, re.S | re.M)
    if not m:
        raise SpecError(f"{REGRESSION}: TESTS=( ... ) array not found")
    for line in m.group(1).splitlines():
        t = line.strip()
        if not t or t.startswith("#"):
            continue
        parts = t.strip('"').split()
        if len(parts) != 2:
            raise SpecError(f"{REGRESSION}: cannot parse TESTS entry {t!r}")
        add(parts[0], parts[1], REGRESSION)
    for script in EXTRA_SCRIPTS:
        if not tree.is_file(script):
            continue
        text = tree.read_text(script)
        found = []
        for line in text.splitlines():
            s = line.strip()
            if s.startswith("#") or "--dry-run" in s:
                continue
            lm = re.search(r"--suite\s+([A-Za-z0-9_.-]+)\s+--mode\s+([A-Za-z0-9_.-]+)", s)
            if lm:
                found.append((lm.group(1), lm.group(2)))
        sv = re.search(r'^suite="([^"]+)"', text, re.M)
        mv = re.search(r'^mode="([^"]+)"', text, re.M)
        if sv and mv:
            found.append((sv.group(1), mv.group(1)))
        if not found:
            raise SpecError(f"{script}: no compiletest suite/mode found")
        for suite, mode in found:
            add(suite, mode, script)
            if "overlays" in text:
                for r in rows:
                    if r["suite"] == suite:
                        r["perf_overlays"] = True
    return rows


def perf_overlays(tree: Tree, suite: str) -> dict:
    """kani-perf.sh: `for d in tests/<suite>/overlays/*/; cp -r $d* tests/<suite>/$(basename $d)/`."""
    base = f"tests/{suite}/overlays"
    mapping = {}
    if not tree.is_dir(base):
        return mapping
    for top in tree.listdir(base):
        top_path = f"{base}/{top}"
        if not tree.is_dir(top_path):
            continue
        for entry in tree.listdir(top_path):
            if entry.startswith("."):
                continue  # shell glob `*` skips dotfiles
            src = f"{top_path}/{entry}"
            targets = tree.walk_files(src) if tree.is_dir(src) else [src]
            for f in targets:
                rel = f[len(top_path) + 1:]
                mapping[f"tests/{suite}/{top}/{rel}"] = tree.real(f)
    return mapping


def is_test_name(name: str) -> bool:
    return name.endswith(".rs") and not name.startswith((".", "#", "~"))


def collect_paths(tree: Tree, suite: str, mode: str):
    """Return (sorted test paths, collection_error)."""
    base = f"tests/{suite}"
    if not tree.is_dir(base):
        return [], f"tests/{suite} does not exist (compiletest panics: Could not read tests)"
    out = []
    if mode in RS_MODES:
        def rec(d):
            for name in tree.listdir(d):
                p = f"{d}/{name}"
                if is_test_name(name):
                    out.append(p)
                elif tree.is_dir(p) and name != "auxiliary":
                    rec(p)
        rec(base)
    elif mode in CARGO_MODES:
        def rec(d):
            has_cargo = tree.exists(f"{d}/Cargo.toml")
            for name in tree.listdir(d):
                p = f"{d}/{name}"
                if has_cargo and (p.endswith(".expected") or name == "expected"):
                    out.append(p)
                elif tree.is_dir(p):
                    rec(p)
        rec(base)
    else:
        for name in tree.listdir(base):
            p = f"{base}/{name}"
            if not tree.exists(f"{p}/config.yml"):
                return sorted(out), f"{p}: no config.yml (compiletest fatal_error aborts collection)"
            out.append(p)
    return sorted(out), None


def parse_exec_config(text: str, where: str) -> dict:
    cfg = {}
    for raw in text.split("\n"):
        line = raw.split(" #", 1)[0].rstrip() if not raw.lstrip().startswith("#") else ""
        if not line.strip():
            continue
        m = re.match(r"^([A-Za-z_]+):\s*(.*)$", line)
        if not m or line[0].isspace():
            raise SpecError(f"{where}: unsupported config.yml line {raw!r}")
        value = m.group(2).strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
            value = value[1:-1]
        cfg[m.group(1)] = value
    unknown = set(cfg) - {"script", "expected", "exit_code"}
    if unknown or "script" not in cfg:
        raise SpecError(f"{where}: config.yml keys {sorted(cfg)} (need script; allowed script/expected/exit_code)")
    code = cfg.get("exit_code")
    return {"script": cfg["script"], "expected": cfg.get("expected") or None,
            "exit_code": int(code) if code not in (None, "") else 0,
            "exit_code_explicit": code not in (None, "")}


def _module_files(tree: Tree, root_file: str, text: str, prefix: list, is_mod_root: bool, seen: set,
                  inherited=()):
    """Resolve `mod x;` declarations to (file, module prefix, text, cfgs), recursively."""
    out = []
    d = root_file.rsplit("/", 1)[0]
    stem = root_file.rsplit("/", 1)[-1][:-3]
    for decl in scan(text)["mod_decls"]:
        segs = prefix + decl["scope"] + [decl["name"]]
        base_dir = d if is_mod_root else f"{d}/{stem}"
        if decl["scope"]:
            base_dir = base_dir + "/" + "/".join(decl["scope"])
        if decl["path_attr"]:
            cands = [f"{d}/{decl['path_attr']}"]
        else:
            cands = [f"{base_dir}/{decl['name']}.rs", f"{base_dir}/{decl['name']}/mod.rs"]
        for c in cands:
            c = _normalize(c)
            if c and tree.is_file(c) and c not in seen:
                seen.add(c)
                child_text = tree.read_text(c)
                child_root = c.endswith("/mod.rs") or bool(decl["path_attr"])
                cfgs = list(inherited) + list(decl.get("cfgs") or [])
                out.append((c, segs, child_text, cfgs))
                out.extend(_module_files(tree, c, child_text, segs, child_root, seen, cfgs))
                break
    return out


def _normalize(path: str):
    parts = []
    for p in path.split("/"):
        if p in ("", "."):
            continue
        if p == "..":
            if not parts:
                return None
            parts.pop()
        else:
            parts.append(p)
    return "/".join(parts)


def _crate_sources(tree: Tree, root: str, harness_prefix=None):
    """[(file, module segments, text)] reachable from one crate root file."""
    if not tree.is_file(root):
        return []
    text = tree.read_text(root)
    seen = {root}
    return [(root, [], text, [])] + _module_files(tree, root, text, [], True, seen)


def cfgs_from_compile_flags(flags: list):
    """`--cfg=feature="x"` / `--cfg x` compile flags -> (features, bare idents)."""
    values = []
    for i, f in enumerate(flags):
        if f.startswith("--cfg="):
            values.append(f[len("--cfg="):])
        elif f == "--cfg" and i + 1 < len(flags):
            values.append(flags[i + 1])
    features, idents = set(), set()
    for v in values:
        m = re.match(r'^feature\s*=\s*"?([^"]*)"?$', v)
        if m:
            features.add(m.group(1))
        elif re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", v):
            idents.add(v)
    return features, idents


def _harnesses_from(sources, crate=None, features=None, tests=False, extra_true=()):
    rows = []
    for f, segs, text, decl_cfgs in sources:
        for h in scan(text)["harnesses"]:
            h = dict(h)
            h["pretty_name"] = "::".join(segs + ([h["pretty_name"]] if h["pretty_name"] else []))
            h["file"] = f
            h["cfgs"] = list(decl_cfgs) + list(h.get("cfgs") or [])
            h["cfg_active"] = all(cfg_active(c, features, tests, extra_true) for c in h["cfgs"])
            if crate is not None:
                h["crate_target"] = crate
            rows.append(h)
    return rows


def select_harnesses(harnesses: list, filters: list, exact: bool) -> None:
    """kani_metadata::find_proof_harnesses; marks `selected` in place."""
    for h in harnesses:
        if not filters:
            h["selected"] = True
        elif exact:
            h["selected"] = h["pretty_name"] in filters
        else:
            unqualified = h["pretty_name"].rsplit("::", 1)[-1]
            h["selected"] = (h["pretty_name"] in filters or unqualified in filters
                             or any(t in h["pretty_name"] for t in filters))


def _flag_values(flags: list, name: str) -> list:
    out = []
    for i, f in enumerate(flags):
        if f == name and i + 1 < len(flags):
            out.append(flags[i + 1])
        elif f.startswith(name + "="):
            out.append(f[len(name) + 1:])
    return out


def metadata_kani_flags(meta: dict) -> list:
    flags = []
    for key, value in sorted((meta.get("flags") or {}).items()):
        if value is True:
            flags.append(f"--{key}")
        elif value is False:
            continue
        elif isinstance(value, list):
            for v in value:
                flags.extend([f"--{key}", str(v)])
        else:
            flags.extend([f"--{key}", str(value)])
    for key, value in sorted((meta.get("unstable") or {}).items()):
        if value:
            flags.extend(["-Z", key])
    return flags


def _digest(tree: Tree, paths) -> tuple:
    inputs = [{"path": p, "sha256": tree.sha256(p)} for p in sorted(set(paths))]
    h = hashlib.sha256()
    for row in inputs:
        h.update(f"{row['path']}\t{row['sha256']}\n".encode())
    return h.hexdigest(), inputs


def build_unit(tree: Tree, suite: str, mode: str, path: str) -> dict:
    base = f"tests/{suite}"
    rel = path[len(base) + 1:]
    unit = {
        "id": f"{suite}/{rel}",
        "suite": suite,
        "mode": mode,
        "path": path,
        "upstream_test_name": f"[{mode}] {suite}/{rel}",
    }
    private = {}
    if mode in RS_MODES:
        text = tree.read_text(path)
        props = parse_props(text, is_rs=True)
        unit["unit_kind"] = "rs-file"
        d = path.rsplit("/", 1)[0]
        expected = None
        if mode == "expected":
            dot = path[:-3] + ".expected"
            expected = dot if tree.exists(dot) else f"{d}/expected"
        elif mode == "coverage-based":
            expected = f"{d}/expected"
        sources = _crate_sources(tree, path)
        cfg_features, cfg_idents = cfgs_from_compile_flags(props["compile_flags"])
        harnesses = _harnesses_from(sources, features=cfg_features, tests=False, extra_true=cfg_idents)
        flags = props["kani_flags"]
        select_harnesses(harnesses, _flag_values(flags, "--harness"), "--exact" in flags)
        inputs = [f for f, _, _, _ in sources]
        for lib in _flag_values(flags, "--c-lib"):
            for cand in (_normalize(lib), _normalize(f"{d}/{lib}")):
                if cand and tree.is_file(cand):
                    inputs.append(cand)
                    break
        exp_exists = expected is not None and tree.is_file(expected)
        if exp_exists:
            inputs.append(expected)
        unit["expected_path"] = expected if exp_exists else None
        if expected is not None and not exp_exists:
            unit["expected_missing"] = expected
        private["src"] = "\n".join(t for _, _, t, _ in sources)
        private["script"] = ""
        unit["cargo"] = None
        unit["exec"] = None
    elif mode in CARGO_MODES:
        text = tree.read_text(path)
        props = parse_props(text, is_rs=False)
        unit["unit_kind"] = "cargo-expected"
        pkg = path.rsplit("/", 1)[0]
        name = path.rsplit("/", 1)[-1]
        harness_filter = None if name == "expected" else (name[:-len(".expected")] if name.endswith(".expected") else name)
        toml_text = tree.read_text(f"{pkg}/Cargo.toml")
        toml_error = None
        try:
            manifest = tomllib.loads(toml_text)
        except tomllib.TOMLDecodeError as exc:
            manifest, toml_error = {}, str(exc)
        package = manifest.get("package") or {}
        workspace = manifest.get("workspace") or {}
        meta = {}
        for src_meta in ((workspace.get("metadata") or {}).get("kani"), (package.get("metadata") or {}).get("kani")):
            if isinstance(src_meta, dict):
                meta.update(src_meta)
        meta_flags = meta.get("flags") if isinstance(meta.get("flags"), dict) else {}
        with_tests = mode == "cargo-kani-test" or meta_flags.get("tests") is True
        roots = _cargo_roots(tree, pkg, manifest, with_tests, meta_flags)
        harnesses = []
        sources_all = []
        for crate, root, features in roots:
            srcs = _crate_sources(tree, root)
            sources_all.extend(srcs)
            harnesses.extend(_harnesses_from(srcs, crate=crate, features=features, tests=with_tests))
        select_harnesses(harnesses, [harness_filter] if harness_filter else [], False)
        other_expected = {p for p in tree.walk_files(pkg)
                          if p != path and p.rsplit("/", 1)[0] == pkg and (p.endswith(".expected") or p.endswith("/expected"))}
        inputs = [p for p in tree.walk_files(pkg) if p not in other_expected and "/target/" not in f"{p}/"[len(pkg):]]
        for dep_dir in _path_dependency_dirs(manifest, pkg):
            inputs.extend(p for p in tree.walk_files(dep_dir) if p.endswith((".rs", ".toml", ".c", ".h")))
        unit["expected_path"] = path
        unit["cargo"] = {
            "manifest_dir": pkg,
            "harness_filter": harness_filter,
            "tests_flag": mode == "cargo-kani-test",
            "coverage_flag": mode == "cargo-coverage",
            "metadata_kani": _jsonable(meta),
            "metadata_kani_flags": metadata_kani_flags(meta),
            "workspace": bool(workspace),
            "crate_targets": [c for c, _, _ in roots],
            "cargo_toml_error": toml_error,
        }
        unit["exec"] = None
        private["src"] = "\n".join(t for _, _, t, _ in sources_all)
        private["script"] = ""
        private["toml"] = toml_text
    else:
        props = parse_props(None, is_rs=False)
        unit["unit_kind"] = "exec-dir"
        cfg = parse_exec_config(tree.read_text(f"{path}/config.yml"), f"{path}/config.yml")
        files = tree.walk_files(path)
        rs_files = [f for f in files if f.endswith(".rs")]
        harnesses = []
        for f in rs_files:
            for h in scan(tree.read_text(f))["harnesses"]:
                h = dict(h)
                h["file"] = f
                h["selected"] = None
                h["cfg_active"] = all(cfg_active(c, None, False) for c in h.get("cfgs") or [])
                harnesses.append(h)
        expected = f"{path}/{cfg['expected']}" if cfg["expected"] else None
        unit["expected_path"] = expected if expected and tree.is_file(expected) else None
        if expected and not tree.is_file(expected):
            unit["expected_missing"] = expected
        script_path = _normalize(f"{path}/{cfg['script']}")
        unit["exec"] = {"script": cfg["script"], "script_exists": bool(script_path and tree.is_file(script_path)),
                        "expected": cfg["expected"], "exit_code": cfg["exit_code"],
                        "exit_code_explicit": cfg["exit_code_explicit"]}
        unit["cargo"] = None
        inputs = files
        private["src"] = "\n".join(tree.read_text(f) for f in rs_files)
        private["script"] = "\n".join(tree.read_text(f) for f in files if f.endswith((".sh", ".py")) or f == script_path)
        private["toml"] = "\n".join(tree.read_text(f) for f in files if f.endswith("Cargo.toml"))
    desc = test_description(path, mode, props)
    unit["ignored"] = desc["ignore_message"] if desc["ignore"] else None
    unit["should_fail"] = desc["should_panic"]
    unit["directives"] = {
        "compile_flags": props["compile_flags"],
        "kani_flags": props["kani_flags"],
        "cbmc_flags": props["cbmc_flags"],
        "edition": props["edition"],
        "kani_fail_step": props["kani_fail_step"],
        "should_fail": props["should_fail_directive"],
    }
    if props["kani_fail_step"] is not None and mode != "kani":
        unit["directive_panics"] = True  # header.rs check_kani panics outside Mode::Kani
    if props["multiple_fail_steps"]:
        unit["directive_panics"] = True
    harnesses.sort(key=lambda h: (h.get("file", ""), h["line"], h["pretty_name"]))
    unit["harnesses"] = harnesses
    unit["sha256"], unit["inputs"] = _digest(tree, inputs)
    expected_text = tree.read_text(unit["expected_path"]) if unit.get("expected_path") else None
    private["expected"] = expected_text
    return unit, private


def _jsonable(v):
    if isinstance(v, dict):
        return {k: _jsonable(v[k]) for k in sorted(v)}
    if isinstance(v, list):
        return [_jsonable(x) for x in v]
    if isinstance(v, (str, int, float, bool)) or v is None:
        return v
    return str(v)


def default_features(manifest: dict) -> set:
    """The `default` feature closure of one manifest (dependency features ignored)."""
    table = manifest.get("features") or {}
    out, todo = set(), list(table.get("default", []))
    while todo:
        feat = todo.pop()
        if feat in out or "/" in feat or feat.startswith("dep:"):
            continue
        out.add(feat)
        todo.extend(table.get(feat, []))
    return out


def _package_roots(tree: Tree, pkg: str, manifest: dict, with_tests: bool, label: str = ""):
    roots = []
    features = default_features(manifest)
    lib = manifest.get("lib") or {}
    lib_path = lib.get("path") or "src/lib.rs"
    if tree.is_file(f"{pkg}/{lib_path}"):
        roots.append((f"{label}lib", _normalize(f"{pkg}/{lib_path}"), features))
    declared = set()
    for b in manifest.get("bin") or []:
        p = b.get("path") or (f"src/bin/{b.get('name')}.rs" if b.get("name") else None)
        if p and tree.is_file(f"{pkg}/{p}"):
            roots.append((f"{label}bin:{b.get('name', p)}", _normalize(f"{pkg}/{p}"), features))
            declared.add(_normalize(f"{pkg}/{p}"))
    if tree.is_file(f"{pkg}/src/main.rs") and _normalize(f"{pkg}/src/main.rs") not in declared:
        roots.append((f"{label}bin:main", _normalize(f"{pkg}/src/main.rs"), features))
    if tree.is_dir(f"{pkg}/src/bin"):
        for name in tree.listdir(f"{pkg}/src/bin"):
            p = f"{pkg}/src/bin/{name}"
            if name.endswith(".rs") and tree.is_file(p) and p not in declared:
                roots.append((f"{label}bin:{name[:-3]}", p, features))
    if with_tests and tree.is_dir(f"{pkg}/tests"):
        for name in tree.listdir(f"{pkg}/tests"):
            p = f"{pkg}/tests/{name}"
            if name.endswith(".rs") and tree.is_file(p):
                roots.append((f"{label}test:{name[:-3]}", p, features))
    return roots


def _cargo_roots(tree: Tree, pkg: str, manifest: dict, with_tests: bool, meta_flags=None):
    """Crate roots `cargo kani` builds in `pkg` (no --workspace on the command line).

    cargo builds the root package, or the declared default-members, or every
    member of a virtual manifest; Kani's metadata flags `workspace = true`,
    `package = [...]` and `exclude = [...]` override that selection.
    """
    meta_flags = meta_flags or {}
    workspace = manifest.get("workspace") or {}
    packages = []  # (label, dir, manifest)
    if manifest.get("package") is not None or not manifest:
        packages.append(("", pkg, manifest, (manifest.get("package") or {}).get("name")))
    for member in workspace.get("members") or []:
        if any(ch in member for ch in "*?["):
            continue
        mdir = _normalize(f"{pkg}/{member}")
        if not mdir or mdir == pkg or not tree.is_file(f"{mdir}/Cargo.toml"):
            continue
        try:
            sub = tomllib.loads(tree.read_text(f"{mdir}/Cargo.toml"))
        except tomllib.TOMLDecodeError:
            sub = {}
        packages.append((f"{member}:", mdir, sub, (sub.get("package") or {}).get("name")))
    selected_pkgs = meta_flags.get("package")
    if isinstance(selected_pkgs, str):
        selected_pkgs = [selected_pkgs]
    excluded = meta_flags.get("exclude")
    if isinstance(excluded, str):
        excluded = [excluded]
    if selected_pkgs:
        chosen = [p for p in packages if p[3] in selected_pkgs]
    elif meta_flags.get("workspace") is True:
        chosen = [p for p in packages if not excluded or p[3] not in excluded]
    elif workspace.get("default-members"):
        wanted = {_normalize(f"{pkg}/{m}") or pkg for m in workspace["default-members"]}
        chosen = [p for p in packages if p[1] in wanted]
    elif manifest.get("package") is not None or not manifest:
        chosen = packages[:1]
    else:
        chosen = packages
    roots = []
    for label, pdir, pman, _ in chosen:
        roots.extend(_package_roots(tree, pdir, pman, with_tests, label))
    return roots


def _path_dependency_dirs(manifest: dict, pkg: str):
    dirs = set()
    tables = []
    for key in ("dependencies", "dev-dependencies", "build-dependencies"):
        tables.append(manifest.get(key) or {})
        tables.append(((manifest.get("workspace") or {}).get(key)) or {})
    for table in tables:
        for spec in table.values():
            if isinstance(spec, dict) and isinstance(spec.get("path"), str):
                d = _normalize(f"{pkg}/{spec['path']}")
                if d and not d.startswith(pkg + "/") and d != pkg:
                    dirs.add(d)
    for member in ((manifest.get("workspace") or {}).get("members") or []):
        d = _normalize(f"{pkg}/{member}")
        if d and not d.startswith(pkg + "/") and "*" not in member:
            dirs.add(d)
    return sorted(dirs)
