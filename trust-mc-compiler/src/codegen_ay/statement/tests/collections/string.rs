// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! String collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;
use crate::codegen_ay::names::{RUST_STRING_CONS, RUST_STRING_SORT, struct_sort};
use crate::codegen_ay::stubs::StubKind;

// -----------------------------------------------------------------------------
// String operation codegen tests (stubs/string.rs)
// -----------------------------------------------------------------------------

const STRING_BOOL_PROBE_SOURCE: &str = r#"
pub fn probe_bool(x: bool) -> bool { x }
"#;

const STRING_RET_PROBE_SOURCE: &str = r#"
pub fn probe_string() -> String { String::new() }
"#;

fn with_string_codegen<F>(source: &str, fn_suffix: &str, callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>) + Send,
{
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_suffix);
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        callback(&mut codegen);
    });
}

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    destination: &Place,
) -> Option<Expr> {
    let dest_base = codegen.ssa_base_name(destination);
    codegen.env_lookup(&dest_base).cloned()
}

fn assert_empty_args_leave_destination_unassigned(stub_kind: StubKind, callee_path: &str) {
    with_string_codegen(COLLECTIONS_PROBE_SOURCE, "probe_u32", |codegen| {
        let dest = local_place(0);
        let result = codegen.codegen_string_stub(stub_kind, &[], &dest, Some(1), callee_path);
        assert_eq!(result, None, "{stub_kind:?} with empty args must fail-closed (#2497)");
        assert!(
            assigned_expr_for_place(codegen, &dest).is_none(),
            "{stub_kind:?} with empty args should not assign destination"
        );
    });
}

// --- codegen_string_stub MIR-driven tests ---

/// Test StringNew assigns a concrete String value to destination.
#[test]
fn test_codegen_string_stub_new_assigns_string_destination() {
    with_string_codegen(STRING_RET_PROBE_SOURCE, "probe_string", |codegen| {
        let dest = local_place(0);
        let result =
            codegen.codegen_string_stub(StubKind::StringNew, &[], &dest, Some(1), "String::new");
        assert_eq!(result, Some(1));
        let assigned =
            assigned_expr_for_place(codegen, &dest).expect("StringNew should assign destination");
        assert_eq!(assigned.sort().datatype_name(), Some(RUST_STRING_SORT));
        let len =
            assigned.clone().field_select(RUST_STRING_SORT, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap = assigned.field_select(RUST_STRING_SORT, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test StringFrom assigns String and emits the cap>=len invariant.
#[test]
fn test_codegen_string_stub_from_assigns_string_and_constraint() {
    with_string_codegen(STRING_RET_PROBE_SOURCE, "probe_string", |codegen| {
        let dest = local_place(0);
        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let result =
            codegen.codegen_string_stub(StubKind::StringFrom, &[], &dest, Some(2), "String::from");
        assert_eq!(result, Some(2));
        let assigned =
            assigned_expr_for_place(codegen, &dest).expect("StringFrom should assign destination");
        assert_eq!(assigned.sort().datatype_name(), Some(RUST_STRING_SORT));
        assert!(
            codegen.ctx.bmc_vc.constraints.len() > constraints_before,
            "StringFrom should emit at least one invariant constraint"
        );
    });
}

/// Test arg-guarded branches: empty args should early-return without destination assignment.
#[test]
fn test_codegen_string_stub_arg_guards_do_not_assign_destination() {
    for (stub_kind, callee_path) in [
        (StubKind::StringLen, "String::len"),
        (StubKind::StringIsEmpty, "String::is_empty"),
        (StubKind::StringPush, "String::push"),
        (StubKind::StringClear, "String::clear"),
        (StubKind::StringClone, "String::clone"),
        (StubKind::StringTruncate, "String::truncate"),
        (StubKind::StringPushStr, "String::push_str"),
    ] {
        assert_empty_args_leave_destination_unassigned(stub_kind, callee_path);
    }
}

/// Test StringFromUtf8Lossy fallback assigns a symbolic String to destination.
#[test]
fn test_codegen_string_stub_from_utf8_lossy_assigns_symbolic_string() {
    with_string_codegen(STRING_RET_PROBE_SOURCE, "probe_string", |codegen| {
        let dest = local_place(0);
        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let result = codegen.codegen_string_stub(
            StubKind::StringFromUtf8Lossy,
            &[],
            &dest,
            Some(10),
            "String::from_utf8_lossy",
        );
        assert_eq!(result, Some(10));
        let assigned = assigned_expr_for_place(codegen, &dest)
            .expect("StringFromUtf8Lossy should assign destination");
        assert_eq!(assigned.sort().datatype_name(), Some(RUST_STRING_SORT));
        assert!(
            codegen.ctx.bmc_vc.constraints.len() > constraints_before,
            "StringFromUtf8Lossy should emit at least one invariant constraint"
        );
    });
}

/// Test StringEq empty-args fallback assigns symbolic bool.
#[test]
fn test_codegen_string_stub_eq_empty_args_assigns_symbolic_bool() {
    with_string_codegen(STRING_BOOL_PROBE_SOURCE, "probe_bool", |codegen| {
        let dest = local_place(0);
        let result =
            codegen.codegen_string_stub(StubKind::StringEq, &[], &dest, Some(11), "String::eq");
        assert_eq!(result, None, "StringEq with empty args must fail-closed (#2497)");
        assert!(
            assigned_expr_for_place(codegen, &dest).is_none(),
            "StringEq with empty args should not assign destination"
        );
    });
}

/// Test DisplayToString with empty args returns None (fail-closed #2497).
#[test]
fn test_codegen_string_stub_display_to_string_empty_args_fail_closed() {
    with_string_codegen(STRING_RET_PROBE_SOURCE, "probe_string", |codegen| {
        let dest = local_place(0);
        let result = codegen.codegen_string_stub(
            StubKind::DisplayToString,
            &[],
            &dest,
            Some(13),
            "ToString::to_string",
        );
        assert_eq!(result, None, "DisplayToString with empty args must fail-closed (#2497)");
    });
}

/// Test FmtFormat conversion fallback assigns symbolic String value.
#[test]
fn test_codegen_string_stub_fmt_format_assigns_symbolic_string() {
    with_string_codegen(STRING_RET_PROBE_SOURCE, "probe_string", |codegen| {
        let dest = local_place(0);
        let result =
            codegen.codegen_string_stub(StubKind::FmtFormat, &[], &dest, Some(14), "fmt::format");
        assert_eq!(result, Some(14));
        let assigned = assigned_expr_for_place(codegen, &dest)
            .expect("FmtFormat conversion fallback should assign destination");
        assert_eq!(assigned.sort().datatype_name(), Some(RUST_STRING_SORT));
    });
}

// --- String: real-operand tests ---

/// Helper: create a String datatype expression for seeding.
fn make_test_string(len: u64, cap: u64) -> Expr {
    let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
    let string_sort = struct_sort(
        RUST_STRING_SORT,
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", array_sort),
        ],
    );
    let ptr = Expr::bitvec_const(0x2000u64, POINTER_WIDTH);
    let len_expr = Expr::bitvec_const(len, POINTER_WIDTH);
    let cap_expr = Expr::bitvec_const(cap, POINTER_WIDTH);
    let default_byte = Expr::bitvec_const(0u64, 8);
    let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default_byte);

    let ctor_name = string_sort
        .datatype_default_constructor()
        .map_or_else(|| RUST_STRING_CONS.to_string(), str::to_string);
    Expr::datatype_constructor(
        RUST_STRING_SORT,
        ctor_name,
        vec![ptr, len_expr, cap_expr, data],
        string_sort,
    )
}

/// Test StringLen with a seeded String extracts fld_len.
/// string.rs: StringLen branch.
#[test]
fn test_codegen_string_len_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let str_op = seed_collections_local(&mut codegen, 1, make_test_string(5, 10));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::StringLen,
            &[str_op],
            &dest,
            Some(1),
            "alloc::string::String::len",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("StringLen should assign destination");
        assert!(dest_val.sort().is_bitvec(), "StringLen should produce bitvec sort");
    });
}

/// Test StringIsEmpty with a seeded String produces boolean.
/// string.rs: StringIsEmpty branch.
#[test]
fn test_codegen_string_is_empty_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let str_op = seed_collections_local(&mut codegen, 1, make_test_string(0, 0));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::StringIsEmpty,
            &[str_op],
            &dest,
            Some(1),
            "alloc::string::String::is_empty",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("StringIsEmpty should assign dest");
        assert!(dest_val.sort().is_bool(), "StringIsEmpty should produce Bool sort");
    });
}

/// Test StringPush with a seeded String updates the env with incremented len.
/// string.rs: StringPush branch — symbolic len increment [1,4].
#[test]
fn test_codegen_string_push_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let original_str = make_test_string(5, 16);
        let str_op = seed_collections_local(&mut codegen, 1, original_str.clone());
        let dest = Place { local: 0, projection: vec![] };
        let str_base = Place { local: 1, projection: vec![] };
        let base_name = codegen.ssa_base_name(&str_base);
        let result = codegen.codegen_string_stub(
            StubKind::StringPush,
            &[str_op],
            &dest,
            Some(1),
            "alloc::string::String::push",
        );
        assert_eq!(result, Some(1));
        // Verify env was mutated: string at local 1 should have incremented len
        let updated =
            codegen.env_lookup(&base_name).expect("String should still be in env after push");
        assert!(updated.sort().is_datatype(), "Updated String should be datatype");
        assert_ne!(*updated, original_str, "StringPush should mutate the String in env");
    });
}

/// Test StringClone with a seeded String copies to destination.
/// string.rs: StringClone branch.
#[test]
fn test_codegen_string_clone_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let str_op = seed_collections_local(&mut codegen, 1, make_test_string(8, 16));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::StringClone,
            &[str_op],
            &dest,
            Some(1),
            "alloc::string::String::clone",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("StringClone should assign dest");
        assert!(dest_val.sort().is_datatype(), "StringClone should produce String datatype");
    });
}

/// Test StringClear with a seeded String sets len to zero.
/// string.rs: StringClear branch.
#[test]
fn test_codegen_string_clear_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let original_str = make_test_string(10, 20);
        let str_op = seed_collections_local(&mut codegen, 1, original_str.clone());
        let dest = Place { local: 0, projection: vec![] };
        let str_base = Place { local: 1, projection: vec![] };
        let base_name = codegen.ssa_base_name(&str_base);
        let result = codegen.codegen_string_stub(
            StubKind::StringClear,
            &[str_op],
            &dest,
            Some(1),
            "alloc::string::String::clear",
        );
        assert_eq!(result, Some(1));
        // Verify env was mutated: string at local 1 should have len=0
        let updated =
            codegen.env_lookup(&base_name).expect("String should still be in env after clear");
        assert!(updated.sort().is_datatype(), "Cleared String should be datatype");
        assert_ne!(*updated, original_str, "StringClear should mutate the String in env");
    });
}

/// Test StringTruncate with a seeded String and new_len operand.
/// string.rs: StringTruncate branch — min(old_len, new_len).
#[test]
fn test_codegen_string_truncate_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let original_str = make_test_string(10, 20);
        let str_op = seed_collections_local(&mut codegen, 1, original_str.clone());
        let new_len =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(5u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let str_base = Place { local: 1, projection: vec![] };
        let base_name = codegen.ssa_base_name(&str_base);
        let result = codegen.codegen_string_stub(
            StubKind::StringTruncate,
            &[str_op, new_len],
            &dest,
            Some(1),
            "alloc::string::String::truncate",
        );
        assert_eq!(result, Some(1));
        // Verify env was mutated: string at local 1 should have truncated len
        let updated =
            codegen.env_lookup(&base_name).expect("String should still be in env after truncate");
        assert!(updated.sort().is_datatype(), "Truncated String should be datatype");
        assert_ne!(*updated, original_str, "StringTruncate should mutate the String in env");
    });
}

/// Test StringEq with two seeded Strings produces boolean.
/// string.rs: StringEq branch — quantified forall comparison.
#[test]
fn test_codegen_string_eq_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = seed_collections_local(&mut codegen, 1, make_test_string(5, 10));
        let rhs = seed_collections_local(&mut codegen, 2, make_test_string(5, 10));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::StringEq,
            &[lhs, rhs],
            &dest,
            Some(1),
            "alloc::string::String::eq",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("StringEq should assign dest");
        assert!(dest_val.sort().is_bool(), "StringEq should produce Bool sort");
    });
}
