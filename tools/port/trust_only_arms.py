#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Add the `#[cfg(trust_toolchain)]` match arms for variants only the Trust API has.

Trust's rustc_public adds `Operand::RuntimeChecks`, `AssertMessage::NullReferenceConstructed`
and `ValueAbi::ScalableVector`. Every exhaustive match over those enums needs an arm,
and what that arm must do is a per-site soundness decision, so it is recorded here
as data rather than inferred: one row per match, keyed by file, enclosing fn, the
scrutinee text and the 1-based ordinal of that `match SCRUTINEE` inside the fn.

Decision kinds (the `why` column):

  no-place   A runtime-checks flag is a bool the compiler fixes at codegen time. It
             has no place, local, provenance or pointee, so the arm takes the exit
             the `Constant` arm takes for exactly that reason (or the site's
             "not applicable" exit when the Constant arm inspects the constant).
  value      The site produces the operand's value: `runtime_checks_value`, the
             policy the nightly `NullOp::RuntimeChecks` codegen already applies.
  type       The site needs the operand's type: `bool`, which is what Trust's own
             `Operand::ty` returns for `RuntimeChecks`.
  delegate   The Constant arm defers to `codegen_operand`, which has a value arm.
  invariant  Kani-built instrumentation operands are places; unreachable like Constant.
  label      A new assertion kind; reuse the label of its nearest sibling.
  sibling    `NullReferenceConstructed` is null-pointer UB like `NullPointerDereference`
             (upstream Kani handles them in one arm): same property kind, so it counts
             as a non-panic failure under `#[kani::should_panic]`, and the same gating
             by the memory-safety-checks switch.
  new-abi    A new layout shape; behaves like its nearest sibling (`Vector`).
  new-abi-closed
             A new layout shape at a site whose contract is conservative (anything it
             does not recognise answers the fail-closed value): the arm answers that value
             instead of borrowing `Vector`'s, so an unmodelled shape can only demote.

The script is idempotent: a match with an arm whose PATTERN names the variant is
left alone. The name appearing anywhere else in the match (an arm body, a comment,
a nested match) does not count: behind a catch-all arm the compiler raises no
E0004, so treating such a match as covered would let the catch-all silently absorb
the Trust-only variant.

A row that no longer finds its match is an error, so a rebase that moved code
fails loudly instead of silently skipping an arm. Every row is processed and every
stale row reported before the script exits non-zero, so one refactor on main shows
its whole blast radius in a single run.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from rust_lex import IDENT, PUNCT, Code  # noqa: E402
from trust_api_codemod import match_arms  # noqa: E402

REPO = Path(__file__).resolve().parents[2]
SRC = REPO / "trust-mc-compiler" / "src"
CFG_TRUST = "#[cfg(trust_toolchain)]"

VALUE = "Some(Expr::bool_const(crate::rustc_compat::runtime_checks_value(checks)))"
BOOL_TY = "rustc_public::ty::Ty::bool_ty()"

# (file, fn, scrutinee, ordinal, pattern, body, why)
# pattern: "RC(x)" means `<Operand path>::RuntimeChecks(x)`; anything else is literal.
ROWS = [
    ("codegen_ay/chc/call/codegen_call_c_body.rs", "operand_place", "op", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/cmp_raw_pointer.rs", "operand_is_raw_pointer_like", "operand", 1, "RC(_)", "return false", "no-place"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/math_const.rs", "try_extract_const_f32", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/math_const.rs", "try_extract_const_f64", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/math_const.rs", "try_extract_const_i32", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/misc_intrinsics_pointer.rs", "extract_pointee_size", "operand", 1, "RC(_)", BOOL_TY, "type"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/misc_intrinsics_write_bytes.rs", "operand_pointee_ty", "operand", 1, "RC(_)", BOOL_TY, "type"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/pow.rs", "try_extract_const_u128", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_cmp_string/slice_contains.rs", "resolve_target_value", "arg", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_coroutine_elision_mentions.rs", "operand_mentions_local", "operand", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/call/codegen_call_coroutine_support.rs", "resolve_coroutine_call_arg_state_idx", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_coroutine_support.rs", "resolve_coroutine_call_arg_root_expr", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_misc/referent_resolve.rs", "operand_local_is_ref_like", "arg", 1, "RC(_)", "return false", "no-place"),
    ("codegen_ay/chc/call/codegen_call_misc/referent_resolve_chain.rs", "resolve_ref_chain_to_array", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_slice_provenance.rs", "register_index_tracking_impl", "slice_arg", 1, "RC(_)", "return", "no-place"),
    ("codegen_ay/chc/call/codegen_call_string/codegen_call_string_backing.rs", "propagate_str_as_bytes_metadata", "arg", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_string/codegen_call_string_nth.rs", "try_extract_const_str_bytes", "arg", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_struct_vec_accessor/codegen_call_struct_vec_accessor_scan.rs", "extract_stored_value", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/codegen_call_virtual_inline/gap_classify.rs", "operand_refs_missing", "operand", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/call/codegen_call_virtual_inline/slice_index_trace.rs", "operand_source_place", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/call/inline_shared/place.rs", "inline_operand_to_expr", "operand", 1, "RC(checks)", VALUE, "value"),
    ("codegen_ay/chc/expr/codegen_expr.rs", "translate_operand_with_modified", "operand", 1, "RC(checks)", VALUE, "value"),
    ("codegen_ay/chc/expr/codegen_expr_env.rs", "translate_operand_with_env", "operand", 1, "RC(checks)", VALUE, "value"),
    ("codegen_ay/chc/expr/codegen_expr_signedness.rs", "operand_signedness", "operand", 1, "RC(_)", "operand.ty(self.body.locals()).ok().and_then(ty_signedness)", "type"),
    ("codegen_ay/chc/expr/codegen_expr_signedness.rs", "operand_signedness_for_cast", "operand", 1, "RC(_)", "operand.ty(self.body.locals()).ok().and_then(ty_signedness_for_cast)", "type"),
    ("codegen_ay/chc/rules/codegen_rules_pointer_check.rs", "operand_depends_on_ref_target", "operand", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/stmt/codegen_stmt_assign_simple_single_assign.rs", "operand_has_single_assign_source", "operand", 1, "RC(_)", "true", "no-place"),
    ("codegen_ay/chc/stmt/codegen_stmt_copy.rs", "resolve_copy_intrinsic_target", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/stmt/codegen_stmt_rvalue_binop.rs", "place_of", "op", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/stmt/codegen_stmt_rvalue_pun_scan.rs", "operand_uses_local", "op", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/stmt/codegen_stmt_rvalue_pun_scan.rs", "operand_is_bare_deref_of_local", "op", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/stmt/codegen_stmt_rvalue_pun_scan.rs", "operand_is_bare_local", "op", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/call_uf_table.rs", "operand_is_pure", "operand", 1, "RC(_)", "true", "no-place"),
    ("codegen_ay/chc/float_assertion_patterns.rs", "try_extract_const_u128", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/modifies_frame.rs", "resolve_modifies_footprint", "arg", 1, "RC(_)", "return", "no-place"),
    ("codegen_ay/chc/codegen_ctx_dead_locals.rs", "collect_operand_local", "operand", 1, "RC(_)", "{}", "no-place"),
    ("codegen_ay/chc/stub_codegen/stubs_util_collections.rs", "extract_local_index", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/stub_codegen/stubs_hashmap_resolve.rs", "translate_key_through_deref", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/stub_codegen/stubs_util_flattened_enum.rs", "resolve_flattened_enum_discr", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/stub_codegen/stubs_util_flattened_enum.rs", "resolve_flattened_enum_discr_by_value", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/stub_codegen/stubs_util_flattened_enum.rs", "resolve_flattened_enum_payload", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/stub_codegen/stubs_util_pointer.rs", "resolve_ref_operand", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/loop_unroll/const_trip.rs", "operand", "op", 1, "RC(checks)", "Some(Val::Bool(crate::rustc_compat::runtime_checks_value(checks)))", "value"),
    ("codegen_ay/shadow_mem.rs", "layout_mask_from_operand", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/memory_swap.rs", "typed_swap_pointee", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/codegen_assign_helpers.rs", "track_aggregate_ref_pointees", "operand", 1, "RC(_)", "{}", "no-place"),
    ("codegen_ay/statement/codegen_assign_slice_cast.rs", "try_construct_slice_datatype_from_cast", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/codegen_copy.rs", "try_eval_const_operand", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/codegen_place_value.rs", "get_value_through_ref_source_inner", "operand", 1, "RC(_)", "self.codegen_operand(operand).map(|expr| (expr, RefValueSource::Unreported))", "delegate"),
    ("codegen_ay/statement/codegen_place_value.rs", "get_option_payload_value", "operand", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/statement/codegen_sort.rs", "infer_sort_from_operand", "operand", 1, "RC(_)", "Self::infer_sort_from_ty(rustc_public::ty::Ty::bool_ty())", "type"),
    ("codegen_ay/statement/codegen_sort.rs", "assert_label_for_message", "msg", 1, "AssertMessage::NullReferenceConstructed", '"raw_ptr_deref_null"', "label"),
    ("codegen_ay/statement/comparison/ord_array.rs", "resolve_ord_operand_to_array", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/comparison/raw_eq.rs", "codegen_raw_eq", "operand", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/statement/comparison/raw_eq.rs", "is_raw_eq_zst", "operand", 1, "RC(_)", "Some(rustc_public::ty::Ty::bool_ty())", "type"),
    ("codegen_ay/statement/comparison_eq/partial_ord_array.rs", "resolve_partial_ord_operand_to_array", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/dispatch/apply_closure.rs", "build_apply_closure_receiver", "closure_arg", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/dispatch/array_cmp.rs", "flattened_option_is_some_guard", "option_arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/dispatch/array_cmp.rs", "resolve_operand_to_array", "arg", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/dispatch/closure_call.rs", "translate_rust_call_tuple_args", "tuple_arg", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/dispatch/closure_call.rs", "translate_tuple_field_values", "tuple_arg", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/dispatch/inline_body.rs", "translate_inline_arg_value", "operand", 1, "RC(_)", "(Vec::new(), Vec::new())", "no-place"),
    ("codegen_ay/statement/dispatch/inline_body.rs", "translate_inline_arg_value", "operand", 2, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/dispatch/pow.rs", "try_extract_const_u128", "operand", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/statement/dispatch/ptr_arithmetic.rs", "record_offset_ptr_provenance", "ptr_arg", 1, "RC(_)", "return", "no-place"),
    ("codegen_ay/statement/dispatch/ptr_arithmetic.rs", "record_offset_ptr_provenance", "count_arg", 1, "RC(_)", "return", "no-place"),
    ("codegen_ay/statement/dispatch/stub_dispatch_memory.rs", "record_slice_ptr_provenance", "arg", 1, "RC(_)", "return", "no-place"),
    ("codegen_ay/statement/foreign_frame.rs", "havoc_pointee_of_arg_bmc", "arg", 1, "RC(_)", "return false", "no-place"),
    ("codegen_ay/statement/collections/iter_adapters.rs", "record_adapter_stage", "&args[1]", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/collections/iter_filter_map_replay.rs", "try_concrete_filter_map_collect_from_mir", "op", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/intrinsics/math_const_fold.rs", "try_extract_f32_const", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/intrinsics/math_const_fold.rs", "try_extract_f64_const", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/intrinsics/math_const_fold.rs", "try_extract_i32_const", "operand", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/statement/operand.rs", "codegen_operand", "operand", 1, "RC(checks)", VALUE, "value"),
    ("codegen_ay/statement/rvalue.rs", "codegen_ptr_metadata", "operand", 1, "RC(_)", "Some(Expr::bitvec_const(0, POINTER_WIDTH))", "no-place"),
    ("kani_middle/points_to/points_to_analysis.rs", "successors_for_operand", "operand", 1, "RC(_)", "HashSet::new()", "no-place"),
    ("kani_middle/points_to/points_to_analysis.rs", "successors_for_deref", "operand", 1, "RC(_)", "HashSet::new()", "no-place"),
    ("kani_middle/transform/array_iter.rs", "detect_array_into_iter", "&args[0]", 1, "RC(_)", "return None", "no-place"),
    ("kani_middle/transform/check_uninit/delayed_ub/initial_target_visitor.rs", "push_operand", "operand", 1, "RC(_)", "{}", "no-place"),
    ("kani_middle/transform/check_uninit/relevant_instruction.rs", "operand_ty", "operand", 1, "RC(_)", 'unreachable!(\n    "SetRef/CheckRef/CreateUnion/LoadArgument/StoreArgument operand must be Copy or Move, not RuntimeChecks"\n)', "invariant"),
    ("kani_middle/transform/check_values/mod.rs", "transmute_scalar_source", "op", 1, "checks @ RC(_)", "checks.clone()", "no-place"),
    ("kani_middle/transform/check_values/mod.rs", "try_from_ty", "layout_value_abi!(shape)", 1, "ValueAbi::ScalableVector { .. }", "None", "new-abi"),
    # m3/soundness-fixes-1 (f4fa7d325): `false` = "value validity is not free", so the
    # kani::mem predicate takes the exact register lane or fails closed.
    ("codegen_ay/statement/dispatch/stub_dispatch_simple.rs", "kani_mem_ty_validity_free", "&layout_value_abi!(shape)", 1, "ValueAbi::ScalableVector { .. }", "false", "new-abi-closed"),
    ("kani_middle/transform/inline/remap.rs", "remap_operand", "operand", 1, "RC(checks)", "Operand::RuntimeChecks(checks.clone())", "no-place"),
    ("kani_middle/transform/inline/remap.rs", "remap_assert_message", "msg", 1, "AssertMessage::NullReferenceConstructed", "msg.clone()", "no-place"),
    ("kani_middle/transform/inline/variadic.rs", "operand_mentions", "operand", 1, "RC(_)", "false", "no-place"),
    ("kani_middle/transform/loop_contracts/smt2.rs", "operand_to_smt2", "operand", 1, "RC(_)", "None", "no-place"),
    ("kani_middle/transform/stubs.rs", "copyable_receiver", "operand", 1, "RC(_)", "None", "no-place"),
    ("kani_middle/tuple_usage.rs", "check_operand_whole_use", "operand", 1, "RC(_)", "{}", "no-place"),
    ("kani_middle/tuple_usage.rs", "operand_ty", "operand", 1, "RC(_)", "Some(rustc_public::ty::Ty::bool_ty())", "type"),
    # Revealed once the Rvalue::Use shape errors were gone (second Trust pass).
    ("codegen_ay/chc/call/codegen_call_fn_inline.rs", "unique_def_const_operand", "operand", 1, "RC(_)", "{\n    let lit = self.translate_call_arg_for_inline(operand, &HashSet::new())?;\n    return try_eval_to_const(&lit);\n}", "delegate"),
    ("codegen_ay/chc/call/codegen_call_virtual_inline/gap_classify.rs", "classify_rvalue_gap", "operand", 1, "RC(_)", '"const"', "no-place"),
    # 1657228d3 (2026-09-26) added this closure match with no row, so the check stayed
    # green while the Trust lane failed E0004; the arm landed with the Trust migration.
    ("codegen_ay/chc/call/codegen_call_virtual_inline/statement_exec.rs", "rvalue_carries_address", "operand", 1, "RC(_)", "false", "no-place"),
    ("codegen_ay/chc/loop_modifies_frame.rs", "resolve_const_usize", "op", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/loop_modifies_frame.rs", "resolve_ptr_chain", "op", 1, "RC(_)", "return None", "no-place"),
    ("codegen_ay/chc/stub_codegen/layout_trace.rs", "try_extract_layout_pair_from_operand", "op", 1, "RC(_)", "None", "no-place"),
    ("codegen_ay/chc/stub_codegen/layout_trace.rs", "try_extract_usize_from_operand", "op", 1, "RC(_)", "None", "no-place"),
    ("kani_middle/transform/check_uninit/relevant_instruction.rs", "mk_ref", "operand", 1, "RC(_)", 'unreachable!("mk_ref requires a place operand (Copy or Move), not RuntimeChecks")', "invariant"),
    ("kani_middle/transform/inline/body_inline.rs", "inline_function", "env_arg", 1, "RC(checks)", "rvalue_use!(Rvalue::Use(Operand::RuntimeChecks(checks.clone())))", "no-place"),
    ("kani_middle/transform/inline/body_inline.rs", "inline_function", "&call_args[1]", 1, "RC(_)", 'unreachable!("tuple_arg_is_place check ensures this")', "invariant"),
    ("kani_middle/transform/inline/body_inline.rs", "inline_function", "env_arg", 2, "RC(checks)", "rvalue_use!(Rvalue::Use(Operand::RuntimeChecks(checks.clone())))", "no-place"),
    ("kani_middle/transform/inline/body_inline.rs", "inline_function", "arg_operand", 1, "RC(checks)", "rvalue_use!(Rvalue::Use(Operand::RuntimeChecks(checks.clone())))", "no-place"),
    ("kani_middle/transform/inline/devirtualize.rs", "trace_receiver_concrete_type", "receiver", 1, "RC(_)", "return None", "no-place"),
    ("kani_middle/transform/inline/devirtualize.rs", "trace_receiver_concrete_type", "operand", 1, "RC(_)", BOOL_TY, "type"),
    ("kani_middle/transform/loop_contracts/rule.rs", "apply_loop_rule", "&plan.closure_arg", 1, "checks @ RC(_)", "checks.clone()", "no-place"),
    ("kani_middle/transform/range_iter.rs", "detect_range_into_iter", "&args[0]", 1, "RC(_)", "return None", "no-place"),
    # AssertMessage matches with a wildcard arm: without these rows the new variant would be
    # an `Assertion` (a panic, and an `assume` under --prove-safety-only) instead of null UB.
    ("codegen_ay/chc/expr/codegen_expr_assert.rs", "mir_assert_kind_and_message", "msg", 1, "rustc_public::mir::AssertMessage::NullReferenceConstructed", "PropertyKind::NullPointer", "sibling"),
    ("codegen_ay/chc/expr/codegen_expr_assert.rs", "emit_assert_error_rule_shared", "msg", 1, "Some(rustc_public::mir::AssertMessage::NullReferenceConstructed)", "PropertyKind::NullPointer", "sibling"),
    ("codegen_ay/chc/rules/codegen_rules/transition_gen_terminators.rs", "assert_check_disabled", "msg", 1, "AssertMessage::NullReferenceConstructed", "!ctx.memory_safety_checks", "sibling"),
]


class StaleRow(Exception):
    """A row no longer matches the code it was written for (e.g. after a rebase)."""


def find_fn_body(code: Code, name: str) -> list[tuple[int, int]]:
    bodies = []
    for k in range(len(code) - 1):
        if code.text(k) == "fn" and code.kind(k) == IDENT and code.text(k + 1) == name:
            b = k + 2
            while b < len(code) and code.text(b) not in ("{", ";"):
                if code.text(b) in ("(", "[") and code.m[b] >= 0:
                    b = code.m[b]
                b += 1
            if code.text(b) == "{" and code.m[b] >= 0:
                bodies.append((b, code.m[b]))
    return bodies


def find_match(code: Code, body: tuple[int, int], scrutinee: str, ordinal: int) -> int | None:
    seen = 0
    for k in range(body[0], body[1]):
        if code.text(k) != "match" or code.kind(k) != IDENT:
            continue
        j = k + 1
        while j < body[1] and code.text(j) != "{":
            if code.text(j) in ("(", "[") and code.m[j] >= 0:
                j = code.m[j]
            j += 1
        if "".join(code.text(q) for q in range(k + 1, j)) == scrutinee:
            seen += 1
            if seen == ordinal:
                return j
    return None


def operand_prefix(code: Code, open_idx: int) -> str | None:
    for k in range(open_idx + 1, code.m[open_idx]):
        if code.kind(k) == IDENT and code.text(k) in ("Copy", "Move", "Constant") and code.text(k - 1) == "::":
            start = code.path_start(k - 2)
            return "".join(code.text(q) for q in range(start, k - 1))
    return None


def apply_row(src: str, row) -> tuple[str, str]:
    rel, fn, scrutinee, ordinal, pattern, body, why = row
    code = Code(src)
    bodies = find_fn_body(code, fn)
    open_idx = None
    for b in bodies:
        open_idx = find_match(code, b, scrutinee, ordinal)
        if open_idx is not None:
            break
    if open_idx is None:
        raise StaleRow(f"trust_only_arms: {rel}: no `match {scrutinee}` #{ordinal} in fn {fn}")
    if pattern.startswith("RC(") or " @ RC(" in pattern:
        variant = "RuntimeChecks"
        prefix = operand_prefix(code, open_idx)
        if prefix is None:
            raise StaleRow(f"trust_only_arms: {rel}: fn {fn}: match has no Operand arms")
        pattern = pattern.replace("RC(", f"{prefix}::RuntimeChecks(")
    else:
        variant = re.search(r"(NullReferenceConstructed|ScalableVector|RuntimeChecks)", pattern).group(1)
    arms = match_arms(code, open_idx)
    if not arms:
        raise StaleRow(f"trust_only_arms: {rel}: fn {fn}: cannot split match arms")
    wildcard = next((i for i, arm in enumerate(arms) if is_catch_all(code, arm)), None)
    # Present only when some arm's pattern names the variant, and that arm must not sit behind
    # a catch-all arm, where it would be unreachable. A mention outside every pattern (a body,
    # a comment, a nested match) covers nothing, so it falls through to insertion.
    for i, arm in enumerate(arms):
        pa, pb = arm["pat"]
        if any(code.text(k) == variant for k in range(pa, pb + 1)):
            if wildcard is not None and wildcard < i:
                raise StaleRow(
                    f"trust_only_arms: {rel}: fn {fn}: `{variant}` arm follows a catch-all arm and is unreachable"
                )
            return src, "present"
    first = code.t[arms[0]["start"]]
    line_start = src.rfind("\n", 0, first.start) + 1
    indent = src[line_start:first.start]
    body_lines = body.split("\n")
    body_text = body_lines[0] + "".join(f"\n{indent}{line}" for line in body_lines[1:])
    if wildcard is not None:
        # a specific arm must precede the catch-all or the catch-all swallows the variant
        insert_at = code.t[arms[wildcard]["start"]].start
        arm = f"{CFG_TRUST}\n{indent}{pattern} => {body_text},\n{indent}"
        return src[:insert_at] + arm + src[insert_at:], "added"
    last = arms[-1]
    insert_at = code.t[last["end"]].end
    lead = ""
    if code.text(last["end"]) != "," and code.text(last["body"][1]) != "}":
        lead = ","
    arm = f"{lead}\n{indent}{CFG_TRUST}\n{indent}{pattern} => {body_text},"
    return src[:insert_at] + arm + src[insert_at:], "added"


def is_catch_all(code: Code, arm: dict) -> bool:
    """`_`, `_ if ..`, or a bare binding (`other`, `other if ..`, `ref x`): matches any variant."""
    pa, pb = arm["pat"]
    toks = [code.text(k) for k in range(pa, pb + 1)]
    if "if" in toks:
        toks = toks[: toks.index("if")]
    if toks[:1] == ["ref"]:
        toks = toks[1:]
    if toks[:1] == ["mut"]:
        toks = toks[1:]
    if len(toks) != 1:
        return False
    tok = toks[0]
    return tok == "_" or (code.kind(pa) == IDENT and tok[:1].islower() and tok not in ("true", "false"))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument(
        "--check", action="store_true", help="exit 1 if any arm is missing; do not write (2 if any row is stale)"
    )
    args = ap.parse_args(argv)
    by_file: dict[str, list] = {}
    for row in ROWS:
        by_file.setdefault(row[0], []).append(row)
    added = 0
    stale: list[str] = []
    for rel, rows in sorted(by_file.items()):
        path = SRC / rel
        try:
            src = path.read_text(encoding="utf-8")
        except FileNotFoundError:
            stale.extend(f"trust_only_arms: {rel}: file not found (fn {row[1]})" for row in rows)
            continue
        original = src
        for row in rows:
            try:
                src, status = apply_row(src, row)
            except StaleRow as err:
                stale.append(str(err))
                continue
            if status == "added":
                added += 1
                print(f"{rel}: fn {row[1]}: match {row[2]} #{row[3]}: {row[6]}")
        if src != original and not args.check:
            path.write_text(src, encoding="utf-8")
    for message in stale:
        print(message, file=sys.stderr)
    verb = "missing" if args.check else "added"
    print(f"trust_only_arms: {added} arms {verb}; {len(ROWS)} rows; {len(stale)} stale", file=sys.stderr)
    if stale:
        return 2
    return 1 if args.check and added else 0


if __name__ == "__main__":
    sys.exit(main())
