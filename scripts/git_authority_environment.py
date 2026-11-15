#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Keep Git authority reads independent of ambient configuration and grafts."""
import os
import re
import subprocess
import sys


def git_environment():
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith('GIT_')}
    environment.update(
        GIT_CONFIG_GLOBAL=os.devnull,
        GIT_CONFIG_NOSYSTEM='1',
        GIT_GRAFT_FILE=os.devnull,
        GIT_NO_REPLACE_OBJECTS='1',
        GIT_NO_LAZY_FETCH='1',
        GIT_TERMINAL_PROMPT='0',
        GIT_OPTIONAL_LOCKS='0',
    )
    return environment


def git_transport_environment(root):
    """Permit configured credentials for fetches without importing Git authority.

    Cargo's Git subprocesses need the user's credential helper on private
    remotes. Copy only credential settings into the isolated environment;
    global URL rewrites, grafts, object stores and other configuration remain
    excluded. Local history checks continue to use git_environment directly.
    """
    discovery = {key: value for key, value in os.environ.items()
                 if not key.startswith('GIT_')}
    result = subprocess.run(
        ['git', '-C', str(root), 'config', '--null', '--get-regexp',
         r'^credential(\..*)?\.(helper|username|usehttppath)$'],
        env=discovery, capture_output=True, timeout=10,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError('could not read configured Git credential settings')
    environment = git_environment()
    settings = []
    for entry in result.stdout.split(b'\0'):
        if not entry:
            continue
        key, separator, value = entry.partition(b'\n')
        if not separator or not re.fullmatch(
                rb'credential(?:\..*)?\.(?:helper|username|usehttppath)', key):
            raise RuntimeError('invalid Git credential setting')
        settings.append((os.fsdecode(key), os.fsdecode(value)))
    environment['GIT_CONFIG_COUNT'] = str(len(settings))
    for index, (key, value) in enumerate(settings):
        environment[f'GIT_CONFIG_KEY_{index}'] = key
        environment[f'GIT_CONFIG_VALUE_{index}'] = value
    return environment


if __name__ == '__main__':
    os.execvpe('git', ['git', *sys.argv[1:]], git_environment())
