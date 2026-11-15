# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
import unittest

from fixture import TOOL_DIR  # noqa: F401
from kani_spec.rustscan import cfg_active, scan


class RustScanTests(unittest.TestCase):
    def names(self, src):
        return [(h["pretty_name"], h["kind"], h["should_panic"]) for h in scan(src)["harnesses"]]

    def test_pretty_names_follow_inline_modules_and_fn_bodies(self):
        src = ("#[cfg(kani)]\nmod verify {\n  #[kani::proof]\n  fn a() {}\n  mod deeper { #[kani::proof] fn b() {} }\n}\n"
               "#[kani::proof]\nfn top() { #[kani::proof] fn inner() {} }\n")
        self.assertEqual([n for n, _, _ in self.names(src)], ["verify::a", "verify::deeper::b", "top", "top::inner"])

    def test_attribute_spellings(self):
        src = ("#[cfg_attr(kani, kani::proof, kani::unwind(3))]\nfn c() {}\n"
               "#[kani::proof_for_contract(foo::bar)]\n#[kani::should_panic]\npub fn d() {}\n"
               "#[kani :: proof]\nconst fn e() {}\n")
        hs = scan(src)["harnesses"]
        self.assertEqual([(h["name"], h["kind"]) for h in hs], [("c", "proof"), ("d", "proof_for_contract"), ("e", "proof")])
        self.assertEqual(hs[0]["unwind"], "3")
        self.assertEqual(hs[1]["contract_target"], "foo::bar")
        self.assertTrue(hs[1]["should_panic"])

    def test_comments_and_strings_are_ignored(self):
        src = ('// #[kani::proof]\n/* #[kani::proof] fn no() {} */\nconst S: &str = "#[kani::proof] fn no2";\n'
               'const C: char = \'{\';\n#[kani::proof]\nfn yes<\'a>() {}\n')
        self.assertEqual([n for n, _, _ in self.names(src)], ["yes"])

    def test_impl_scopes(self):
        src = "struct S;\nimpl S {\n  #[kani::proof]\n  fn m() {}\n}\nimpl Clone for S { fn clone(&self) -> S { S } }\n"
        self.assertEqual([n for n, _, _ in self.names(src)], ["S::m"])

    def test_macro_templates_are_flagged(self):
        src = "macro_rules! gen { ($name:ident) => { #[kani::proof] fn $name() {} }; }\ngen!(x);\n"
        hs = scan(src)["harnesses"]
        self.assertEqual(len(hs), 1)
        self.assertTrue(hs[0]["macro_template"])

    def test_cfg_predicates_are_recorded_and_evaluated(self):
        src = ('#![cfg(feature = "full")]\n#[cfg(disabled)] // needs pthreads\n#[kani::proof]\nfn off() {}\n'
               '#[cfg(not(target_arch = "wasm32"))]\nmod m { #[kani::proof] fn on() {} }\n')
        hs = scan(src)["harnesses"]
        self.assertEqual([(h["pretty_name"], h["cfgs"]) for h in hs],
                         [("off", ['feature="full"', "disabled"]), ("m::on", ['feature="full"', 'not(target_arch="wasm32")'])])
        self.assertFalse(cfg_active("disabled"))
        self.assertTrue(cfg_active('feature = "full"', {"full"}))
        self.assertFalse(cfg_active('feature = "full"', set()))
        self.assertTrue(cfg_active('feature = "full"', None))
        self.assertTrue(cfg_active('not(target_arch = "wasm32")'))
        self.assertFalse(cfg_active("all(test, kani)"))
        self.assertTrue(cfg_active("all(test, kani)", tests=True))
        self.assertTrue(cfg_active("any(kani, loom)"))
        self.assertTrue(cfg_active("loom", extra_true={"loom"}))

    def test_module_declarations(self):
        decls = scan('mod a;\n#[path = "x/y.rs"]\nmod b;\nmod c { mod d; }\n')["mod_decls"]
        self.assertEqual([(d["name"], d["path_attr"], d["scope"]) for d in decls],
                         [("a", None, []), ("b", "x/y.rs", []), ("d", None, ["c"])])


if __name__ == "__main__":
    unittest.main()
