// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec MIR-driven codegen stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;

// --- codegen_vec_stub MIR-driven tests ---

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

fn make_test_vec_for_mir(len: u64, cap: u64) -> Expr {
    let elem_sort = Sort::bitvec(32);
    let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
    let vec_sort_name = "Vec_bv32";
    let vec_sort = struct_sort(
        vec_sort_name,
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", array_sort),
        ],
    );

    let ptr = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);
    let len_expr = Expr::bitvec_const(len, POINTER_WIDTH);
    let cap_expr = Expr::bitvec_const(cap, POINTER_WIDTH);
    let default_elem = Expr::bitvec_const(0u64, 32);
    let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default_elem);

    let ctor_name = vec_sort
        .datatype_default_constructor()
        .map_or_else(|| crate::codegen_ay::names::cons_name(vec_sort_name), str::to_string);
    Expr::datatype_constructor(
        vec_sort_name,
        ctor_name,
        vec![ptr, len_expr, cap_expr, data],
        vec_sort,
    )
}

/// Test codegen_vec_stub VecNew returns target and assigns datatype destination.
/// collections/vec.rs: VecNew branch — no args guard, always constructs Vec.
#[test]
fn test_codegen_vec_stub_new_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_vec_stub(StubKind::VecNew, &[], &dest, Some(1), "alloc::vec::Vec::new");
        assert_eq!(result, Some(1));

        // VecNew always assigns destination with a Vec datatype (even with empty args)
        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("VecNew should assign destination");
        assert!(
            dest_expr.sort().is_datatype(),
            "VecNew should produce datatype sort, got {:?}",
            dest_expr.sort()
        );
    });
}

#[test]
fn test_codegen_vec_stub_new_extra_checks_invalidates_provenance() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        ctx.config.extra_pointer_checks = true;
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_vec_stub(StubKind::VecNew, &[], &dest, Some(1), "alloc::vec::Vec::new");
        assert_eq!(result, Some(1));

        let rendered_constraints = codegen.ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains("false"),
            "extra-pointer-checks Vec::new should store false into obj_valid: {rendered_constraints}"
        );
    });
}

#[test]
fn test_codegen_vec_stub_with_capacity_symbolic_zero_extra_checks_invalidates_conditionally() {
    use crate::codegen_ay::stubs::StubKind;

    const SOURCE: &str = r#"
        pub fn probe_vec_with_capacity(cap: usize) -> usize { cap }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        ctx.config.extra_pointer_checks = true;
        let instance = find_instance_by_suffix(&ctx, "probe_vec_with_capacity");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let cap = Expr::var("symbolic_cap", Sort::bitvec(POINTER_WIDTH));
        let cap_op = seed_collections_local(&mut codegen, 1, cap);
        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_vec_stub(
            StubKind::VecWithCapacity,
            &[cap_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::with_capacity",
        );
        assert_eq!(result, Some(1));

        let rendered_constraints = codegen.ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        // Symbolic cap takes the ITE assertion path: asserts ptr > 0
        // when cap == 0. Provenance array invalidation is deferred (#3392).
        assert!(
            rendered_constraints.contains("(ite ")
                && rendered_constraints.contains("symbolic_cap")
                && rendered_constraints.contains("bvugt"),
            "Vec::with_capacity(symbolic_cap) should conditionally assert ptr > 0 on cap == 0 lane: {rendered_constraints}"
        );
    });
}

/// Test codegen_vec_stub VecPush with insufficient args hits warn path.
/// collections/vec.rs: VecPush branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_push_insufficient_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecPush,
            &[],
            &dest,
            Some(2),
            "alloc::vec::Vec::push",
        );
        assert_eq!(result, None, "insufficient args must fail-closed (#2497)");
        // Fail-closed: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecPush fail-closed path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecPush fail-closed path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecLen with empty args hits warn path.
/// collections/vec.rs: VecLen branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_len_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_vec_stub(StubKind::VecLen, &[], &dest, Some(3), "alloc::vec::Vec::len");
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
        // Fail-closed: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecLen fail-closed path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecLen warn path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecIsEmpty with empty args hits warn path.
/// collections/vec.rs: VecIsEmpty branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_is_empty_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIsEmpty,
            &[],
            &dest,
            Some(4),
            "alloc::vec::Vec::is_empty",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
        // Fail-closed: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecIsEmpty fail-closed path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecIsEmpty warn path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecClear with empty args hits warn path.
/// collections/vec.rs: VecClear branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_clear_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecClear,
            &[],
            &dest,
            Some(5),
            "alloc::vec::Vec::clear",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
        // Fail-closed: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecClear fail-closed path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecClear warn path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecClone with empty args hits warn path.
/// collections/vec.rs: VecClone branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_clone_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecClone,
            &[],
            &dest,
            Some(6),
            "alloc::vec::Vec::clone",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
        // Fail-closed: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecClone fail-closed path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecClone warn path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecPop with empty args hits warn path.
/// collections/vec.rs: VecPop branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_pop_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_vec_stub(StubKind::VecPop, &[], &dest, Some(7), "alloc::vec::Vec::pop");
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
        // Fail-closed: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecPop fail-closed path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecPop warn path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecAsSlice with empty args hits warn path.
/// collections/vec.rs: VecAsSlice branch (warn path — no destination assignment).
#[test]
fn test_codegen_vec_stub_as_slice_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecAsSlice,
            &[],
            &dest,
            Some(8),
            "alloc::vec::Vec::as_slice",
        );
        assert_eq!(result, Some(8));
        // Warn path: no destination assignment, no new constraints
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecAsSlice warn path should not assign destination"
        );
        assert_eq!(
            constraint_count(&codegen),
            before,
            "VecAsSlice warn path should not emit constraints"
        );
    });
}

/// Test codegen_vec_stub VecWithCapacity with a real capacity operand creates Vec datatype.
/// collections/vec.rs: VecWithCapacity branch.
#[test]
fn test_codegen_vec_stub_with_capacity_real_operand_assigns_datatype() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let cap_op =
            seed_collections_local(&mut codegen, 1, Expr::bitvec_const(9u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecWithCapacity,
            &[cap_op],
            &dest,
            Some(9),
            "alloc::vec::Vec::with_capacity",
        );
        assert_eq!(result, Some(9));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val =
            codegen.env_lookup(&dest_base).expect("VecWithCapacity should assign destination");
        assert!(dest_val.sort().is_datatype(), "VecWithCapacity should produce datatype sort");
    });
}

/// Test codegen_vec_stub VecCapacity with a seeded Vec argument returns a bitvector length-like value.
/// collections/vec.rs: VecCapacity branch (non-empty args path).
#[test]
fn test_codegen_vec_stub_capacity_real_operand_assigns_bitvec() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec_for_mir(3, 11));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecCapacity,
            &[vec_op],
            &dest,
            Some(10),
            "alloc::vec::Vec::capacity",
        );
        assert_eq!(result, Some(10));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val =
            codegen.env_lookup(&dest_base).expect("VecCapacity should assign destination");
        assert!(dest_val.sort().is_bitvec(), "VecCapacity should produce bitvec sort");
    });
}

/// Test codegen_vec_stub VecAsPtr with a seeded Vec argument returns a bitvector pointer.
/// collections/vec.rs: VecAsPtr branch (non-empty args path).
#[test]
fn test_codegen_vec_stub_as_ptr_real_operand_assigns_bitvec() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec_for_mir(4, 12));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecAsPtr,
            &[vec_op],
            &dest,
            Some(11),
            "alloc::vec::Vec::as_ptr",
        );
        assert_eq!(result, Some(11));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("VecAsPtr should assign destination");
        assert!(dest_val.sort().is_bitvec(), "VecAsPtr should produce bitvec sort");
    });
}

/// Test codegen_vec_stub VecAsMutPtr with a seeded Vec argument returns a bitvector pointer.
/// collections/vec.rs: VecAsMutPtr branch (non-empty args path).
#[test]
fn test_codegen_vec_stub_as_mut_ptr_real_operand_assigns_bitvec() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec_for_mir(4, 12));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecAsMutPtr,
            &[vec_op],
            &dest,
            Some(12),
            "alloc::vec::Vec::as_mut_ptr",
        );
        assert_eq!(result, Some(12));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val =
            codegen.env_lookup(&dest_base).expect("VecAsMutPtr should assign destination");
        assert!(dest_val.sort().is_bitvec(), "VecAsMutPtr should produce bitvec sort");
    });
}
