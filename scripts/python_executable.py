# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Launch generated Python programs through their exact selected interpreter."""

import shlex


def python_executable_header(interpreter: str) -> str:
    """Use shell exec for interpreter paths with spaces, preserving PID and argv.

    Python reads the shell dispatch as a docstring before the program body.
    """
    # Escape each native backslash for both shell parsing and Python's
    # dispatch docstring; quoted path segments preserve every other character.
    quoted = "\\\\".join(shlex.quote(part) for part in interpreter.split("\\"))
    return "#!/bin/sh\n'''exec' " + quoted + ' "$0" "$@"\n' + "' '''\n"
