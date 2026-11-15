#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/check-codegen-determinism.py: what counts as the same
query (a renaming of declared symbols, declaration order) and what does not
(conjunct order, assertion order, constants)."""

from __future__ import annotations

import importlib.util
import re
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location("check_codegen_determinism",
                                               SCRIPTS / "check-codegen-determinism.py")
det = importlib.util.module_from_spec(_SPEC)
sys.modules["check_codegen_determinism"] = det
_SPEC.loader.exec_module(det)

BASE = """(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(declare-rel inv ((_ BitVec 8) (_ BitVec 8)))
(rule (=> (and (= x #x01) (= y #x02)) (inv x y)))
(query (and (inv x y) (not (= x y))))"""


class StructureTests(unittest.TestCase):
    def same(self, a: str, b: str) -> bool:
        return det.structure(a) == det.structure(b)

    def test_identical_text_is_the_same_query(self):
        self.assertTrue(self.same(BASE, BASE))

    def test_declaration_order_is_not_a_difference(self):
        swapped = BASE.replace("(declare-var x (_ BitVec 8))\n(declare-var y (_ BitVec 8))",
                               "(declare-var y (_ BitVec 8))\n(declare-var x (_ BitVec 8))")
        self.assertNotEqual(swapped, BASE)
        self.assertTrue(self.same(BASE, swapped))

    def test_a_consistent_renaming_is_not_a_difference(self):
        names = {"x": "p", "y": "q", "inv": "rel_7"}
        renamed = re.sub(r"(?<![#\w])(x|y|inv)(?!\w)", lambda m: names[m.group(1)], BASE)
        self.assertIn("(rel_7 p q)", renamed)
        self.assertTrue(self.same(BASE, renamed))

    def test_conjunct_order_is_a_difference(self):
        swapped = BASE.replace("(and (= x #x01) (= y #x02))", "(and (= y #x02) (= x #x01))")
        self.assertFalse(self.same(BASE, swapped))

    def test_assertion_order_is_a_difference(self):
        a = "(declare-const a Bool)\n(declare-const b Bool)\n(assert a)\n(assert (not b))"
        b = "(declare-const a Bool)\n(declare-const b Bool)\n(assert (not b))\n(assert a)"
        self.assertFalse(self.same(a, b))

    def test_swapped_constants_are_a_difference(self):
        # A renaming that also renamed literals would read these as equal; they
        # are different queries.
        swapped = BASE.replace("(= x #x01) (= y #x02)", "(= x #x02) (= y #x01)")
        self.assertFalse(self.same(BASE, swapped))

    def test_builtins_are_not_renamed(self):
        a = "(declare-const a (_ BitVec 8))\n(assert (bvult a #x05))"
        b = "(declare-const a (_ BitVec 8))\n(assert (bvslt a #x05))"
        self.assertFalse(self.same(a, b))

    def test_quoted_symbols_are_renamed(self):
        a = "(declare-const |f::local_1| (_ BitVec 8))\n(assert (= |f::local_1| #x00))"
        b = "(declare-const |g::local_9| (_ BitVec 8))\n(assert (= |g::local_9| #x00))"
        self.assertTrue(self.same(a, b))


if __name__ == "__main__":
    unittest.main()
