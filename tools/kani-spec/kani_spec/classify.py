# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Clause taxonomy and unit classification.

Promoted from the 2026-09-10 audit prototype (build_matrix.py). Clause and
classification rules are lexical and deterministic; they are heuristics that
the overlay's exemption sign-off (plan decision D1) must audit before a class
becomes a closed list. Classes, in precedence order:

1. fixme               upstream ignores the unit or expects it to fail
2. cbmc-specific       exercises CBMC/SAT/goto-C/LLBC behaviour
3. toolchain-dependent needs the exact rustc/std of Kani's nightly
4. cli-surface         kani/cargo-kani command-line behaviour, not a verdict
5. verdict-spec        a backend-independent verification outcome
"""
from __future__ import annotations

import re

CLAUSES = {
 "harness.attribute": ("#[kani::proof] harness declaration and entry semantics", [("src", r"kani::proof\b")]),
 "harness.proof_for_contract": ("#[kani::proof_for_contract] harnesses", [("src", r"kani::proof_for_contract")]),
 "harness.unwind": ("#[kani::unwind], --default-unwind/--unwind, unwinding assertions", [("src", r"kani::unwind"), ("flags", r"unwind"), ("exp", r"unwinding assertion|unwind"), ("path", r"(?i)unwind")]),
 "harness.should_panic": ("#[kani::should_panic] negative verification", [("src", r"kani::should_panic"), ("path", r"should.panic")]),
 "harness.solver_attr": ("#[kani::solver] / --solver selection", [("src", r"kani::solver"), ("flags", r"--solver|solver")]),
 "harness.async": ("async harnesses, kani::block_on/spawn, -Z async-lib schedules", [("src", r"kani::(block_on|spawn|futures|yield_now|RoundRobin)|async fn|\.await"), ("flags", r"async-lib")]),
 "harness.selection": ("--harness/--exact/--function harness selection", [("flags", r"--harness|--exact|--function")]),
 "nondet.any": ("kani::any / any_where nondeterministic values", [("src", r"kani::any\b|kani::any::<|any_where|kani::any_raw|\bany\(\)")]),
 "nondet.arbitrary_derive": ("Arbitrary trait impls and #[derive(Arbitrary)]", [("src", r"Arbitrary"), ("path", r"(?i)arbitrary")]),
 "nondet.bounded_arbitrary": ("BoundedArbitrary / bounded_any", [("src", r"BoundedArbitrary|bounded_any|#\[bounded")]),
 "nondet.collections": ("kani::vec::any_vec / kani::slice::any_slice / nondet slices", [("src", r"any_vec|exact_vec|any_slice|any_slice_of_array"), ("path", r"(?i)nondet.?(slice|vector)|any_vec")]),
 "invariant": ("kani::Invariant, #[derive(Invariant)], #[safety_constraint]", [("src", r"Invariant|safety_constraint")]),
 "assume": ("kani::assume", [("src", r"kani::assume|\bassume\(")]),
 "assert": ("assert!/assert_eq!/kani::assert semantics and messages", [("src", r"\bassert(_eq|_ne)?!|kani::assert\(|debug_assert")]),
 "cover": ("kani::cover! and cover property statuses", [("src", r"kani::cover|\bcover!\("), ("exp", r"SATISFIED|UNSATISFIABLE")]),
 "reachability": ("assertion reachability checks (UNREACHABLE status)", [("exp", r"UNREACHABLE"), ("flags", r"assertion-reach"), ("path", r"(?i)reach")]),
 "check.arithmetic_overflow": ("arithmetic overflow checks", [("exp", r"overflow"), ("path", r"(?i)overflow|arith")]),
 "check.division": ("division/remainder by zero and overflow", [("exp", r"divide by zero|divisor of zero|remainder")]),
 "check.shift": ("shift distance checks", [("exp", r"shift (left|right)|attempt to shift"), ("path", r"(?i)shift")]),
 "check.bounds": ("index out of bounds / slice range checks", [("exp", r"index out of bounds|out of bounds|range end|slice index"), ("flags", r"bounds-check"), ("path", r"(?i)bounds|oob")]),
 "check.pointer_memory_safety": ("pointer dereference, dangling/dead objects, invalid access", [("exp", r"dereference failure|pointer_dereference|dangling|dead object|deallocated|invalid pointer|pointer invalid|null pointer|misaligned"), ("flags", r"pointer-checks|memory-safety"), ("path", r"(?i)dangling|dead|deref|dealloc|realloc|Pointer")]),
 "check.pointer_arithmetic": ("pointer offset/arith_offset/offset_from checks", [("src", r"\.(offset|add|sub|byte_add|offset_from|wrapping_offset)\("), ("path", r"(?i)offset")]),
 "check.panic_unreachable": ("panics, unwrap/expect, unreachable!, abort", [("src", r"panic!|unreachable!|\.unwrap\(\)|\.expect\(|process::abort|todo!|unimplemented!"), ("path", r"(?i)panic|abort|unreachable")]),
 "check.float": ("float semantics, NaN, float_to_int_in_range, float overflow", [("src", r"\bf32\b|\bf64\b|kani::float"), ("flags", r"float"), ("path", r"(?i)float|nan")]),
 "check.intrinsics": ("compiler intrinsics semantics and their UB checks", [("src", r"intrinsics::"), ("path", r"(?i)intrinsic")]),
 "check.uninit": ("-Z uninit-checks memory initialization", [("flags", r"uninit-checks"), ("src", r"MaybeUninit"), ("path", r"(?i)uninit")]),
 "check.valid_value": ("-Z valid-value-checks validity invariants", [("flags", r"valid-value"), ("path", r"(?i)valid.?value")]),
 "check.ub_safety_precondition": ("library safety preconditions / ub_checks / unsafe precondition", [("exp", r"unsafe precondition|safety precondition|ub_checks|safety_check"), ("src", r"ub_checks|check_library_ub|assert_unsafe_precondition")]),
 "check.undefined_function": ("undefined function / unsupported construct reporting", [("flags", r"undefined-function"), ("exp", r"not currently supported|unsupported construct|Unsupported|unsupported_construct|missing function|no body")]),
 "check.default_toggles": ("--no-default-checks / --no-overflow-checks / check selection flags", [("flags", r"--no-default-checks|--no-overflow-checks|--no-memory-safety-checks|--no-unwinding-checks|--no-undefined-function-checks|--prove-safety-only|--no-assert-contracts|--extra-pointer-checks")]),
 "contracts.function": ("#[kani::requires]/#[kani::ensures] function contracts", [("src", r"kani::requires|kani::ensures|kani::proof_for_contract"), ("flags", r"function-contracts")]),
 "contracts.modifies": ("#[kani::modifies] frame conditions and any_modifies", [("src", r"kani::modifies|any_modifies")]),
 "contracts.stub_verified": ("#[kani::stub_verified] contract-as-summary", [("src", r"kani::stub_verified")]),
 "contracts.recursion": ("#[kani::recursion] inductive contract checking", [("src", r"kani::recursion")]),
 "contracts.old_result": ("old()/result in ensures", [("src", r"\bold\(|\|result")]),
 "loop_contracts": ("#[kani::loop_invariant]/loop_modifies/loop_decreases, -Z loop-contracts", [("src", r"kani::loop_invariant|loop_modifies|loop_decreases"), ("flags", r"loop-contracts|synthesize-loop-contracts")]),
 "quantifiers": ("kani::forall!/exists!, -Z quantifiers", [("src", r"forall!|exists!"), ("flags", r"quantifiers")]),
 "mem_predicates": ("kani::mem predicates (can_dereference, can_write, same_allocation, is_inbounds)", [("src", r"kani::mem::|can_dereference|can_write|can_read_unaligned|same_allocation|is_inbounds|checked_size_of_raw"), ("flags", r"mem-predicates")]),
 "stubbing": ("#[kani::stub], stub sets, -Z stubbing", [("src", r"kani::stub\b|kani::stub\(|use_stub_set|stub_set!"), ("flags", r"stubbing"), ("path", r"(?i)stub")]),
 "ghost_state": ("kani::shadow memory, -Z ghost-state", [("src", r"kani::shadow|ShadowMem"), ("flags", r"ghost-state")]),
 "heap_alloc": ("heap allocation, Box/Vec/alloc", [("src", r"Box::new|\bVec\b|vec!|alloc::|HashMap|BTreeMap|VecDeque|String::")]),
 "raw_pointers": ("raw pointers and unsafe", [("src", r"\*const |\*mut |ptr::|unsafe ")]),
 "dyn_vtable": ("trait objects, vtables, function pointers, closures", [("src", r"\bdyn |fn\(|FnOnce|FnMut|Fn\("), ("flags", r"restrict-vtable")]),
 "layout_transmute": ("repr/transmute/size_of/niche/layout", [("src", r"transmute|#\[repr\(|size_of|align_of|MaybeUninit"), ("flags", r"randomize-layout")]),
 "simd": ("SIMD and target features", [("src", r"simd|std::arch|core::arch|target_feature")]),
 "concurrency": ("threads, atomics, sync primitives", [("src", r"std::thread|Mutex|RwLock|Atomic[A-Z]|thread_local!|std::sync|Arc<")]),
 "statics_globals": ("statics, static mut, thread locals", [("src", r"\bstatic (mut )?[A-Z_]")]),
 "fmt_strings": ("strings, formatting, printing", [("src", r"format!|println!|print!|eprintln!|to_string\(|\bstr\b"), ("flags", r"check_debug_fmt")]),
 "ffi_c": ("extern C, C libraries (-Z c-ffi --c-lib), global_asm", [("src", r"extern \"C\"|global_asm|asm!"), ("flags", r"c-ffi|c-lib|ignore-global-asm")]),
 "std_verification": ("std/core library verification (verify-std, std-checks)", [("path", r"^std-checks|verify_std|std_codegen"), ("flags", r"verify-std")]),
 "cargo_workflow": ("cargo kani package/workspace/features/build.rs workflow", [("unit", r"cargo|exec_cargo")]),
 "cli_diagnostics": ("compile-time and CLI diagnostics, attribute validation errors", [("exp_diag", r".")]),
 "unstable_gating": ("-Z unstable feature gating", [("flags", r"-Z|unstable")]),
 "concrete_playback": ("concrete playback test generation", [("flags", r"concrete-playback|playback"), ("path", r"(?i)playback")]),
 "coverage": ("source coverage (--coverage, kani-cov)", [("flags", r"coverage"), ("mode", r"coverage")]),
 "autoharness": ("autoharness generation", [("flags", r"autoharness"), ("path", r"(?i)autoharness|autoderive")]),
 "list": ("kani list / cargo kani list", [("script", r"kani list"), ("path", r"(?i)_list")]),
 "output_formats": ("--output-format regular/terse/old, JSON export, verbosity", [("flags", r"output-format|export-json|--verbose|--quiet|--debug|log-file"), ("path", r"(?i)output-format|json|verbose|quiet|log_file|logging|check-output|individual_file_output")]),
 "timeouts_limits": ("--harness-timeout, --object-bits, parallelism, fail-fast", [("flags", r"harness-timeout|object-bits|--jobs|-j |fail-fast"), ("path", r"(?i)timeout|fail.fast|parallel")]),
 "codegen_only_build": ("--only-codegen/--no-codegen/--gen-c, build and codegen caches", [("flags", r"only-codegen|no-codegen|gen-c"), ("path", r"(?i)codegen|build-cache|compiler_defaults|crate-name")]),
 "llbc_lean": ("Charon/LLBC and Lean output backends", [("flags", r"print-llbc|lean"), ("path", r"^llbc")]),
 "version_meta": ("--version and toolchain identity", [("flags", r"--version"), ("path", r"(?i)version")]),
}

CLI_ONLY_FLAG_RE = re.compile(r"--output-format|--export-json|concrete-playback|--coverage|source-coverage|--version|--verbose|--quiet|--log-file|--harness-timeout|--fail-fast|--only-codegen|--no-codegen|--jobs|--debug|--visualize|--workspace|--manifest-path|--target-dir|--print-llbc|-Zlean|autoharness|--gen-c")
CBMC_CHECK_ARGS_RE = re.compile(r"--(float-overflow|unsigned-overflow|signed-overflow|bounds|pointer|div-by-zero|conversion|undefined-shift|nan|pointer-overflow|memory-leak|pointer-primitive)-check")
CARGO_CLI_PATH_RE = re.compile(r"(?i)(^|/)(ws-|workspace|default-members|config|simple-config-toml|cargo-features-flag|feature-flag|build-rs|cargo-tests-dir|dev-depends|dependency-test|target-selection|supported-lib-types|unsupported-lib-types|symlink|nested-dirs|crate-type|verbose|debug|output-format|unexpected_cfgs|strict-lints|zero-harnesses|no-std-no-kani|unstable-attr|stubbing-flag|multiple-harnesses)")



# Kani's default rendering; naming it changes no verdict or check a unit states.
DEFAULT_OUTPUT_FORMAT_RE = re.compile(r"--output-format(?:\s+|=)regular\b")
# Kani keeps CBMC's bounds and pointer checks on by default and emits Rust's own
# bounds and UB checks in the compiler (kani-driver/src/call_cbmc.rs
# cbmc_check_flags passes --no-bounds-check/--no-pointer-check only when memory
# safety checks are off), so re-enabling them through cbmc-flags does not make
# an oracle CBMC-specific (expected/array, kani/Count/Unstable/C{l,t}tz/bounds).
KANI_NATIVE_CBMC_CHECK_ARGS_RE = re.compile(r"(?<![\w-])--(?:bounds|pointer)-check(?![\w-])")

CLAUSE_TARGETS = ("src", "flags", "exp", "path", "unit", "exp_diag", "mode", "script")


def expected_features(content):
    if content is None:
        return None
    d = {}
    d["status_lines"] = len(re.findall(r"Status: (SUCCESS|FAILURE|UNDETERMINED|UNREACHABLE|SATISFIED|UNSATISFIABLE)", content)) + \
        len(re.findall(r"^\s*(SUCCESS|FAILURE|UNDETERMINED|UNREACHABLE|SATISFIED|UNSATISFIABLE)\\?\s*$", content, re.M))
    d["diag"] = bool(re.search(r"^\s*(error|warning)(\[[A-Z0-9]+\])?:", content, re.M))
    d["rustc_code"] = bool(re.search(r"error\[E\d{4}\]", content))
    d["aborting"] = "error: aborting due to" in content
    d["cbmc_text"] = bool(re.search(r"\bCBMC\b|\bcbmc\b|__CPROVER|\bgoto\b|symtab|kissat|minisat|cadical|SAT solver", content))
    d["kani_limitation"] = bool(re.search(r"not currently supported|unsupported construct|Unsupported|unsupported_construct", content))
    d["std_paths"] = bool(re.search(r"library/(core|std|alloc)/src|/rustc/[0-9a-f]{7,}", content))
    d["unstable_gate"] = bool(re.search(r"requires the unstable|-Z [a-z-]+|--enable-unstable|unstable-options|unstable feature", content))
    d["kani_words"] = bool(re.search(r"kani|Kani|harness|contract|stub|proof", content))
    d["descriptions"] = len(re.findall(r"Description:", content))
    return d


def build_context(unit, private, oracle):
    suite, mode = unit["suite"], unit["mode"]
    rel = unit["id"][len(suite) + 1:]
    directives = unit["directives"]
    script = private.get("script") or ""
    if mode == "exec":
        flags = " ".join(re.findall(r"(?:cargo kani|kani)[^\n|;&]*", script))
    elif unit.get("cargo"):
        flags = " ".join(unit["cargo"]["metadata_kani_flags"])
    else:
        flags = " ".join(directives["kani_flags"] + directives["compile_flags"])
    toml = private.get("toml") or ""
    effective = (oracle or {}).get("effective") or {}
    run_verdict = effective.get("run_verdict")
    if run_verdict is None and not effective and oracle and oracle.get("run_verdict"):
        run_verdict = oracle["run_verdict"]["verdict"]
    verdict = None
    if unit.get("expected_path") and run_verdict is not None:
        verdict = "FAIL" if run_verdict == "FAILED" else "SUCCESS"
    expd = expected_features(private.get("expected"))
    if expd is not None:
        expd["verdict"] = verdict
    has_c = False
    if unit["unit_kind"] == "rs-file":
        has_c = bool(private.get("sibling_c")) and bool(re.search(r'extern "C"', private.get("src") or ""))
    path_for_clauses = rel
    if suite == "llbc":
        path_for_clauses = "llbc/" + rel
    if suite == "std-checks":
        path_for_clauses = "std-checks/" + rel
    return {
        "rel": rel, "suite": suite, "mode": mode, "flags": flags, "src": private.get("src") or "",
        "exp": private.get("expected"), "expd": expd, "script": script,
        "cbmc_flags": directives["cbmc_flags"],
        "stage": "check" if effective.get("stage") == "check" else directives["kani_fail_step"],
        "ext_deps": 0, "workspace": ("[workspace]" in toml and ("members" in toml or mode == "exec")),
        "has_c_files": has_c, "path": path_for_clauses,
        "unit": {"rs-file": "single-file", "cargo-expected": "cargo", "exec-dir": "exec" + ("_cargo" if toml else "")}[unit["unit_kind"]],
    }


def clauses_for(ctx):
    found = []
    for name, (_, rules) in CLAUSES.items():
        for tgt, rx in rules:
            if tgt == "exp_diag":
                if ctx["exp"] is not None and ctx["expd"]["diag"]:
                    found.append(name)
                    break
                continue
            text = ctx.get(tgt) or ""
            if re.search(rx, text):
                found.append(name)
                break
    if not found:
        found = ["cli_diagnostics"] if ctx["mode"] == "exec" else ["harness.attribute"]
    return found


def tags_for(ctx):
    tags = []
    if re.search(r"#!\[feature\(", ctx["src"]):
        tags.append("nightly_feature_gate")
    if "--cbmc-args" in ctx["flags"] or ctx["cbmc_flags"]:
        tags.append("cbmc_args_present")
    expd = ctx["expd"]
    if expd and expd["std_paths"]:
        tags.append("std_source_paths_in_expected")
    if expd and expd["verdict"] is None and ctx["exp"] is not None and not expd["diag"]:
        tags.append("expected_is_check_text_only")
    if re.search(r"kani::solver|--solver", ctx["src"] + " " + ctx["flags"]):
        tags.append("sat_solver_selection")
    if expd and expd["descriptions"]:
        tags.append("per_check_description_text")
    return tags


def classify(ctx):
    rel, suite, mode, flags = ctx["rel"], ctx["suite"], ctx["mode"], ctx["flags"]
    expd = ctx["expd"]
    upath = f"{suite}/{rel}"
    if mode == "kani-fixme":
        return "fixme", "kani-fixme mode: upstream expects this kani test to FAIL (records a known Kani gap)"
    if "fixme" in upath or "ignore" in upath:
        return "fixme", "path contains fixme/ignore: upstream compiletest ignores it (make_test_description, every mode)"
    if suite == "llbc" or re.search(r"print-llbc|-Zlean", flags):
        return "cbmc-specific", "alternate Charon/LLBC/Lean backend output, not a verification verdict"
    if re.search(r"--gen-c", flags + ctx["script"]):
        return "cbmc-specific", "goto-C emission (--gen-c)"
    if CBMC_CHECK_ARGS_RE.search(KANI_NATIVE_CBMC_CHECK_ARGS_RE.sub(" ", flags + " " + " ".join(ctx["cbmc_flags"]))):
        return "cbmc-specific", "enables CBMC-native instrumentation via --cbmc-args, not Rust semantics"
    if re.search(r"(?i)solver-attribute|solver-option|invalid-cbmc-function-arg|simple-kissat|cbmc-unknown-lang-mode|smt-solver-error-status|object-bits|unsupported_num_objects|cbmc", rel):
        return "cbmc-specific", "test purpose is a CBMC/SAT-solver option or limit"
    if expd and expd["cbmc_text"]:
        return "cbmc-specific", "oracle text names CBMC/goto/SAT-solver internals"
    if re.search(r"c-ffi|--c-lib", flags) or ctx["has_c_files"]:
        return "cbmc-specific", "C sources compiled into the goto model (goto-cc); outside a Rust-MIR engine"
    if re.search(r"restrict-vtable", flags):
        return "cbmc-specific", "CBMC function-pointer restriction (-Z restrict-vtable)"
    if expd and expd["kani_limitation"] and expd["verdict"] != "SUCCESS":
        return "cbmc-specific", "oracle records a Kani codegen limitation (unsupported construct); an engine may exceed it"
    if suite == "std-checks" or re.search(r"verify.std", rel + ctx["script"]):
        return "toolchain-dependent", "verifies std/core source of the exact toolchain (needs rust-src matching the compiler)"
    if expd and (expd["rustc_code"] or expd["aborting"]) and not expd["kani_words"] and expd["verdict"] is None:
        return "toolchain-dependent", "oracle is a rustc diagnostic, not a Kani one"
    if re.search(r"mir-opt-level|next-solver|randomize-layout", flags):
        return "toolchain-dependent", "depends on rustc MIR optimisation/trait-solver/layout behaviour"
    if expd and expd["std_paths"]:
        return "toolchain-dependent", "oracle names std source locations of a specific toolchain"
    if mode == "exec":
        return "cli-surface", "script-driven kani/cargo kani command-line test (exit code + output)"
    if mode in ("coverage-based", "cargo-coverage"):
        return "cli-surface", "coverage report format (kani --coverage + kani-cov)"
    m = CLI_ONLY_FLAG_RE.search(DEFAULT_OUTPUT_FORMAT_RE.sub(" ", flags))
    if m:
        return "cli-surface", "exercises a CLI-only option (" + m.group(0) + ")"
    if DEFAULT_OUTPUT_FORMAT_RE.search(flags) and re.search(r"(?i)output-format", rel):
        return "cli-surface", "tests the rendering of the default --output-format regular"
    if expd and expd["verdict"] is None and expd["unstable_gate"] and not expd["status_lines"]:
        return "cli-surface", "unstable-feature gating message of the kani CLI"
    if mode in ("cargo-kani", "cargo-kani-test", "cargo-coverage") and (CARGO_CLI_PATH_RE.search(rel) or ctx["workspace"]):
        return "cli-surface", "cargo package/workspace/target selection behaviour of cargo kani"
    if suite in ("ui", "cargo-ui") and expd and expd["verdict"] is None and not expd["status_lines"] and not expd["kani_words"]:
        return "cli-surface", "UI text with no verdict or harness-language content"
    if expd and expd["verdict"] is None and not expd["status_lines"] and expd["diag"]:
        return "verdict-spec", "harness-language rejection: engine front end must refuse the program (message text via normaliser)"
    if ctx["stage"] == "check":
        return "verdict-spec", "harness-language rejection: kani-check-fail directive (engine front end must refuse the program)"
    return "verdict-spec", "verification outcome is backend-independent"
