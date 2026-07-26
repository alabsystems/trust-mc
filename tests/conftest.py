# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Pytest plugin facade and compatibility exports."""

from tests.fixtures.autospec_helpers import make_run_cmd_mock
from tests.fixtures.subprocess_helpers import REAL_GIT, run_subprocess

pytest_plugins = [
    "tests.fixtures.collection_hooks",
    "tests.fixtures.env_isolation",
    "tests.fixtures.cargo_lock_env",
    "tests.fixtures.domain_fixtures",
]

__all__ = [
    "REAL_GIT",
    "lock_env_context",
    "make_run_cmd_mock",
    "run_subprocess",
]


def lock_env_context(*args, **kwargs):
    """Compatibility wrapper for tests importing lock_env_context from conftest."""
    # Import lazily so pytest can rewrite/assert-load the fixture plugin first.
    from tests.fixtures.cargo_lock_env import lock_env_context as _lock_env_context

    return _lock_env_context(*args, **kwargs)
