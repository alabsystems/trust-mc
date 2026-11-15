#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Check the real locked selected graph and its shared measurement tuple."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys
from git_authority_environment import git_environment
if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib


def validate(metadata: dict, root: Path, ir: str, vc: str, clean: str) -> None:
    packages = metadata.get('packages')
    if not isinstance(packages, list) or metadata.get('resolve') is None:
        raise ValueError('full resolved package graph required')
    required = {'trust-ir', 'trust-ir-build', 'trust-vc-merge-contract', 'clean-kernel'}
    if not required.issubset({p.get('name') for p in packages}):
        raise ValueError('selected shared providers missing from resolved graph')
    seen_names = set()
    for package in packages:
        name = package['name']
        family = next((f for f in ('trust-ir', 'trust-vc', 'clean')
                       if name == f or name.startswith(f + '-')), None)
        if family is None:
            continue
        if name in seen_names:
            raise ValueError(f'{name} has multiple resolved authorities')
        seen_names.add(name)
        if family == 'trust-ir':
            expected = (root.parent / 'trust-ir/crates' / name / 'Cargo.toml').resolve()
            if package.get('source') is not None or Path(package['manifest_path']).resolve() != expected:
                raise ValueError(f'{name} must resolve uniquely to the selected physical sibling')
        else:
            revision = vc if family == 'trust-vc' else clean
            source = f'git+https://github.com/alabsystems/{family}.git?rev={revision}#{revision}'
            if package.get('source') != source:
                raise ValueError(f'{name} must resolve uniquely to exact Git authority {revision}')
    nodes = {n['id']: n for n in metadata['resolve']['nodes']}
    selected = {p['name']: p['id'] for p in packages if p['name'] in ('trust-ir','trust-ir-build','clean-kernel','trust-vc-merge-contract')}
    # The kernel must be on the selected builder's dependency closure, not a
    # disconnected package row that happens to have the requested identity.
    pending = [selected['trust-ir-build']]
    seen = set()
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        if node not in nodes:
            raise ValueError('incomplete resolved graph')
        pending.extend(nodes[node]['dependencies'])
    if selected['clean-kernel'] not in seen:
        raise ValueError('selected builder does not resolve the selected Clean kernel')
    with (root / 'tools/tuple.toml').open('rb') as handle:
        tuple_ = tomllib.load(handle)
    for table, revision in (('trust_ir',ir), ('trust_vc',vc), ('clean',clean)):
        if tuple_.get(table, {}).get('rev') != revision:
            raise ValueError(f'measurement tuple [{table}] disagrees with selected source')


def main() -> int:
    root, targo, ir, vc, clean = sys.argv[1:]
    try:
        output = subprocess.check_output([targo, 'metadata', '--frozen', '--format-version', '1',
                                          '--manifest-path', str(Path(root) / 'Cargo.toml')], text=True, env=git_environment())
        validate(json.loads(output), Path(root), ir, vc, clean)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f'check-shared-pin-graph: error: {error}', file=sys.stderr)
        return 1
    print('check-shared-pin-graph: locked selected graph and tuple agree')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
