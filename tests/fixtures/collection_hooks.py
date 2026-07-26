# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Pytest collection/config hooks used across the test suite."""

from importlib.util import find_spec

import pytest


def pytest_configure(config):
    """Validate required test dependencies are installed."""
    required = (
        ("pytest_timeout", "pytest-timeout"),
        ("hypothesis", "hypothesis"),
    )
    missing = [distribution for module, distribution in required if find_spec(module) is None]
    if missing:
        raise pytest.UsageError(
            f"Required test dependencies not installed: {', '.join(missing)}. "
            "Run: pip install -e '.[test]'"
        )


# Test files that spawn real bash subprocesses need more than the 10s global
# pytest timeout (#4428). Apply timeout(30) to match TEST_SUBPROCESS_TIMEOUT.
_SUBPROCESS_HEAVY_PREFIXES = (
    "tests/test_auth_preflight_keyring",
    "tests/test_bump_git_dep_rev",
    "tests/test_bump_git_dep_rev_url",
    "tests/test_pre_commit_hook",
    "tests/test_pre_commit_stale_tree",
    "tests/test_pre_commit_integration",
    "tests/test_commit_msg_hook_",
    "tests/test_pre_commit_hook_build_gate",
    "tests/test_sync_repo_auto_commit",
    "tests/test_sync_repo_e2e",
    "tests/test_post_commit_hook",
    "tests/test_sync_repo_ops",
    "tests/test_sync_check",
    "tests/test_git_wrapper",
    "tests/test_run_scoped_tests",
    "tests/test_verify_incremental",
    "tests/test_regression_generated_file_exemption",
    "tests/test_pre_commit_regression",
)


def pytest_collection_modifyitems(items):
    """Apply timeout(30) to subprocess-heavy test files (#4428).

    The global timeout is 10s (#1886) but real bash subprocess tests routinely
    take 2-8s per test, breaching 10s under xdist load. This overrides the
    default for known subprocess-heavy files without requiring per-file markers.
    Tests with existing @pytest.mark.timeout decorators are left unchanged.
    """
    for item in items:
        if any(item.nodeid.startswith(p) for p in _SUBPROCESS_HEAVY_PREFIXES):
            if not any(m.name == "timeout" for m in item.iter_markers()):
                item.add_marker(pytest.mark.timeout(30))
