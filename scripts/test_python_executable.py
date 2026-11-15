#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Execute a generated program through a quoted, space-containing interpreter."""

import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest

from python_executable import python_executable_header


class PythonExecutableTests(unittest.TestCase):
    def test_exact_interpreter_arguments_and_process_identity(self):
        with tempfile.TemporaryDirectory(prefix="Python launcher ") as temporary:
            root = Path(temporary)
            for name in ("Python ' $ literal", r"Python \x literal",
                         r"Python \U literal", "Python trailing \\"):
                with self.subTest(interpreter=name):
                    # The path the header executes is witnessed by the shell's `$0`, not by
                    # the child's `sys.executable`: a framework or Homebrew build reports its
                    # own fixed path there whatever path started it. The wrapper records `$0`
                    # and replaces itself with this interpreter, so the PID is unchanged.
                    interpreter = root / name
                    executed = root / "executed path"
                    interpreter.write_text(
                        "#!/bin/sh\n"
                        + f"printf '%s' \"$0\" > {shlex.quote(str(executed))}\n"
                        + f"exec {shlex.quote(sys.executable)} \"$@\"\n"
                    )
                    interpreter.chmod(0o700)
                    program = root / "generated ' program"
                    program.write_text(
                        python_executable_header(str(interpreter))
                        + "import json, os, sys\n"
                        + "print(json.dumps({'pid':os.getpid(), 'argv':sys.argv, 'interpreter':sys.executable}))\n"
                    )
                    program.chmod(0o700)
                    arguments = ["two words", "'\"$*;", ""]
                    with subprocess.Popen([str(program), *arguments], stdout=subprocess.PIPE,
                                          stderr=subprocess.PIPE, text=True) as child:
                        stdout, stderr = child.communicate(timeout=30)
                        self.assertEqual(child.returncode, 0, stderr)
                        observed = json.loads(stdout)
                        self.assertEqual(observed["pid"], child.pid)
                    self.assertEqual(observed["argv"], [str(program), *arguments])
                    self.assertEqual(executed.read_text(), str(interpreter))
                    self.assertTrue(os.path.samefile(observed["interpreter"], sys.executable))


if __name__ == "__main__":
    unittest.main()
