// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;
use crate::codegen_ay::stubs::StubKind;

// -----------------------------------------------------------------------------
// Vec operation codegen tests (collections/vec.rs)
// -----------------------------------------------------------------------------

fn with_vec_codegen<F>(fn_suffix: &str, callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>) + Send,
{
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
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

fn assert_vec_view_empty_args_leave_destination_unassigned(
    stub_kind: StubKind,
    callee_path: &str,
    target: Option<usize>,
) {
    with_vec_codegen("probe_u32", |codegen| {
        let dest = local_place(0);
        let result = codegen.codegen_vec_stub(stub_kind, &[], &dest, target, callee_path);
        assert_eq!(result, target);
        assert!(
            assigned_expr_for_place(codegen, &dest).is_none(),
            "{stub_kind:?} with empty args should not assign destination"
        );
    });
}

// =============================================================================
// Vec stub gap tests (Part of #2016)
// =============================================================================

#[test]
fn test_codegen_vec_view_empty_args_leave_destination_unassigned() {
    for (stub_kind, callee_path, target) in [
        (StubKind::VecAsPtr, "alloc::vec::Vec::as_ptr", Some(1)),
        (StubKind::VecAsMutPtr, "alloc::vec::Vec::as_mut_ptr", Some(2)),
        (StubKind::VecIntoIter, "alloc::vec::Vec::into_iter", Some(3)),
        (StubKind::VecIter, "alloc::vec::Vec::iter", Some(4)),
        (StubKind::VecIterMut, "alloc::vec::Vec::iter_mut", Some(5)),
    ] {
        assert_vec_view_empty_args_leave_destination_unassigned(stub_kind, callee_path, target);
    }
}

// --- Vec: real-operand tests ---

/// Helper: create a Vec datatype expression directly for seeding into env.
fn make_test_vec(len: u64, cap: u64) -> Expr {
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

#[test]
fn test_codegen_vec_view_real_operands_assign_expected_sorts() {
    with_vec_codegen("probe_u32", |codegen| {
        let vec_op = seed_collections_local(codegen, 1, make_test_vec(4, 8));
        for (dest_local, stub_kind, callee_path) in [
            (2, StubKind::VecAsPtr, "alloc::vec::Vec::as_ptr"),
            (3, StubKind::VecAsMutPtr, "alloc::vec::Vec::as_mut_ptr"),
            (4, StubKind::VecIntoIter, "alloc::vec::Vec::into_iter"),
            (5, StubKind::VecIter, "alloc::vec::Vec::iter"),
            (6, StubKind::VecIterMut, "alloc::vec::Vec::iter_mut"),
        ] {
            let dest = local_place(dest_local);
            let result = codegen.codegen_vec_stub(
                stub_kind,
                std::slice::from_ref(&vec_op),
                &dest,
                Some(dest_local),
                callee_path,
            );
            assert_eq!(result, Some(dest_local));
            let assigned =
                assigned_expr_for_place(codegen, &dest).expect("vec view stub should assign dest");
            if matches!(stub_kind, StubKind::VecAsPtr | StubKind::VecAsMutPtr) {
                assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
            } else {
                assert!(assigned.sort().is_datatype());
            }
        }
    });
}

/// Test VecLen with a seeded Vec returns target and assigns bitvec len.
/// vec.rs: VecLen branch — extracts fld_len from Vec datatype.
#[test]
fn test_codegen_vec_len_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a Vec with len=3 at local 1
        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(3, 8));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecLen,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::len",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("VecLen should assign destination");
        assert!(
            dest_val.sort().is_bitvec(),
            "VecLen should produce bitvec sort, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test VecIsEmpty with a seeded Vec returns boolean.
/// vec.rs: VecIsEmpty branch — len == 0.
#[test]
fn test_codegen_vec_is_empty_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(0, 0));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIsEmpty,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::is_empty",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val =
            codegen.env_lookup(&dest_base).expect("VecIsEmpty should assign destination");
        assert!(dest_val.sort().is_bool(), "VecIsEmpty should produce Bool sort");
    });
}

/// Test VecPush with a seeded Vec and value updates the env.
/// vec.rs: VecPush branch — appends element, increments len.
#[test]
fn test_codegen_vec_push_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed Vec at local 1 and a value to push at local 2
        let original_vec = make_test_vec(2, 4);
        let vec_op = seed_collections_local(&mut codegen, 1, original_vec.clone());
        let val_op = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(42u64, 32));
        let dest = Place { local: 0, projection: vec![] };
        let vec_base = Place { local: 1, projection: vec![] };
        let base_name = codegen.ssa_base_name(&vec_base);
        let result = codegen.codegen_vec_stub(
            StubKind::VecPush,
            &[vec_op, val_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::push",
        );
        assert_eq!(result, Some(1));
        // Verify env was mutated: vec at local 1 should be updated
        let updated =
            codegen.env_lookup(&base_name).expect("Vec should still be in env after push");
        assert!(updated.sort().is_datatype(), "Updated Vec should be datatype");
        assert_ne!(*updated, original_vec, "VecPush should mutate the Vec in env");
    });
}

/// Test VecClone with a seeded Vec clones the value to destination.
/// vec.rs: VecClone branch — structural copy.
#[test]
fn test_codegen_vec_clone_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(5, 10));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecClone,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::clone",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("VecClone should assign destination");
        assert!(dest_val.sort().is_datatype(), "VecClone should produce datatype sort");
    });
}

/// Test VecPop with a seeded non-empty Vec produces Option<T>.
/// vec.rs: VecPop branch — pops last element, returns Option.
#[test]
fn test_codegen_vec_pop_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(3, 8));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecPop,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::pop",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("VecPop should assign destination");
        // VecPop returns Option<T> which is a datatype
        assert!(dest_val.sort().is_datatype(), "VecPop should produce Option datatype sort");
    });
}

/// Test VecClear with a seeded Vec resets length to zero.
/// vec.rs: VecClear branch — len = 0, preserving ptr/cap/data.
#[test]
fn test_codegen_vec_clear_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let original_vec = make_test_vec(5, 10);
        let vec_op = seed_collections_local(&mut codegen, 1, original_vec.clone());
        let dest = Place { local: 0, projection: vec![] };
        let vec_base = Place { local: 1, projection: vec![] };
        let base_name = codegen.ssa_base_name(&vec_base);
        let result = codegen.codegen_vec_stub(
            StubKind::VecClear,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::clear",
        );
        assert_eq!(result, Some(1));
        // Verify env was mutated: vec at local 1 should have len=0
        let updated =
            codegen.env_lookup(&base_name).expect("Vec should still be in env after clear");
        assert!(updated.sort().is_datatype(), "Cleared Vec should be datatype");
        assert_ne!(*updated, original_vec, "VecClear should mutate the Vec in env");
    });
}

/// Test VecAsSlice with a seeded Vec produces Slice datatype.
/// vec.rs: VecAsSlice branch — creates Slice{ptr, len, data}.
#[test]
fn test_codegen_vec_as_slice_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(4, 8));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecAsSlice,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::as_slice",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val =
            codegen.env_lookup(&dest_base).expect("VecAsSlice should assign destination");
        assert!(dest_val.sort().is_datatype(), "VecAsSlice should produce Slice datatype");
    });
}

/// Test VecReserve updates capacity to satisfy len+additional and preserves len.
#[test]
fn test_codegen_vec_reserve_real_operand_updates_capacity() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(1, 1));
        let additional = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(100u64, 64));
        let dest = local_place(0);
        let vec_base = local_place(1);
        let base_name = codegen.ssa_base_name(&vec_base);

        let result = codegen.codegen_vec_stub(
            StubKind::VecReserve,
            &[vec_op, additional],
            &dest,
            Some(1),
            "alloc::vec::Vec::reserve",
        );
        assert_eq!(result, Some(1));
        let updated = codegen.env_lookup(&base_name).cloned().expect("Vec should remain in env");
        let cap =
            StatementCodegen::vec_field_select(&updated, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        let len =
            StatementCodegen::vec_field_select(&updated, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap_smt = cap.to_string();
        assert!(
            cap_smt.contains("(ite (bvult") && cap_smt.contains("#x0000000000000064"),
            "VecReserve should encode max(old_cap, len+100) growth, got {cap_smt}"
        );
        let len_smt = len.to_string();
        assert!(
            len_smt.contains("(fld_len"),
            "VecReserve should preserve length field, got {len_smt}"
        );
    });
}

/// Test VecReserveExact grows capacity by the requested amount.
#[test]
fn test_codegen_vec_reserve_exact_real_operand_updates_capacity() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(1, 1));
        let additional = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(1u64, 64));
        let dest = local_place(0);
        let vec_base = local_place(1);
        let base_name = codegen.ssa_base_name(&vec_base);

        let result = codegen.codegen_vec_stub(
            StubKind::VecReserveExact,
            &[vec_op, additional],
            &dest,
            Some(1),
            "alloc::vec::Vec::reserve_exact",
        );
        assert_eq!(result, Some(1));
        let updated = codegen.env_lookup(&base_name).cloned().expect("Vec should remain in env");
        let cap =
            StatementCodegen::vec_field_select(&updated, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        let cap_smt = cap.to_string();
        assert!(
            cap_smt.contains("(ite (bvult") && cap_smt.contains("#x0000000000000001"),
            "VecReserveExact should encode max(old_cap, len+additional), got {cap_smt}"
        );
    });
}

/// Test VecShrinkToFit sets capacity to current length while preserving data.
#[test]
fn test_codegen_vec_shrink_to_fit_sets_cap_to_len() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(2, 8));
        let dest = local_place(0);
        let vec_base = local_place(1);
        let base_name = codegen.ssa_base_name(&vec_base);

        let result = codegen.codegen_vec_stub(
            StubKind::VecShrinkToFit,
            &[vec_op],
            &dest,
            Some(1),
            "alloc::vec::Vec::shrink_to_fit",
        );
        assert_eq!(result, Some(1));
        let updated = codegen.env_lookup(&base_name).cloned().expect("Vec should remain in env");
        let cap =
            StatementCodegen::vec_field_select(&updated, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        let len =
            StatementCodegen::vec_field_select(&updated, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap_smt = cap.to_string();
        let len_smt = len.to_string();
        assert!(
            cap_smt.contains("(fld_len"),
            "VecShrinkToFit should set cap to len expression, got {cap_smt}"
        );
        assert!(
            len_smt.contains("#x0000000000000002") || len_smt.contains("(_ bv2 64)"),
            "VecShrinkToFit should preserve len=2, got {len_smt}"
        );
    });
}

/// Test VecDrop is modeled as a no-op on verifier state.
#[test]
fn test_codegen_vec_drop_is_noop() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let original_vec = make_test_vec(3, 8);
        let vec_op = seed_collections_local(&mut codegen, 1, original_vec.clone());
        let dest = local_place(0);
        let vec_base = local_place(1);
        let base_name = codegen.ssa_base_name(&vec_base);
        let result = codegen.codegen_vec_stub(
            StubKind::VecDrop,
            &[vec_op],
            &dest,
            Some(1),
            "<alloc::vec::Vec<T, A> as std::ops::Drop>::drop",
        );
        assert_eq!(result, Some(1));
        let updated = codegen.env_lookup(&base_name).expect("Vec should remain in env");
        assert_eq!(*updated, original_vec, "VecDrop should not mutate verifier state");
    });
}
