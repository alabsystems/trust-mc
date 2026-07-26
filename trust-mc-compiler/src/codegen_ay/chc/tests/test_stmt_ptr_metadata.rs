// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct regression tests for `codegen_stmt_ptr_metadata.rs`.
//!
//! Part of #3801: dedicated coverage for `translate_ptr_metadata()` and its
//! branch ordering across thin pointers, subslices, tracked lengths, Vec-backed
//! slices, dyn-trait metadata, and symbolic fallback accounting.

#![allow(clippy::panic, clippy::unwrap_used)]

use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::{
    Body, CastKind, Operand, PointerCoercion, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};

use super::common::*;

const THIN_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub fn probe_thin_ref_metadata(x: &u32) {
        let _ = std::ptr::metadata(x);
    }

    pub fn probe_thin_raw_metadata(x: *const u32) {
        let _ = std::ptr::metadata(x);
    }

    pub fn probe_thin_fn_metadata(f: fn(u32) -> u32) {
        let raw: *const fn(u32) -> u32 = &f;
        let _ = std::ptr::metadata(raw);
    }
"#;

const UNRESOLVED_WIDE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub fn probe_unresolved_slice_metadata(slice: &[u32]) -> usize {
        std::ptr::metadata(slice)
    }
"#;

const SUBSLICE_RANGE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub fn probe_subslice_range_metadata() -> usize {
        let arr = [1u32, 2, 3, 4, 5];
        let slice = &arr[1..4];
        std::ptr::metadata(slice)
    }
"#;

const SUBSLICE_RANGE_INCLUSIVE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub fn probe_subslice_range_inclusive_metadata() -> usize {
        let arr = [1u32, 2, 3, 4, 5];
        let slice = &arr[1..=3];
        std::ptr::metadata(slice)
    }
"#;

const BOXED_STR_METADATA_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub fn probe_boxed_str_metadata() -> usize {
        let s = String::from("hello");
        let boxed = s.into_boxed_str();
        let raw: *const str = &*boxed;
        std::ptr::metadata(raw)
    }
"#;

const TUPLE_WRAPPER_METADATA_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub struct CnfClause(Vec<i32>);

    impl CnfClause {
        pub fn unit(lit: i32) -> Self {
            Self(vec![lit])
        }

        pub fn literals(&self) -> &[i32] {
            &self.0
        }
    }

    pub fn probe_clause_metadata(lit: i32) -> usize {
        let clause = CnfClause::unit(lit);
        let slice = clause.literals();
        std::ptr::metadata(slice)
    }
"#;

const DYN_METADATA_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    trait Counter {
        fn count(&self) -> u32;
    }

    struct FixedCounter;

    impl Counter for FixedCounter {
        fn count(&self) -> u32 {
            1
        }
    }

    pub fn probe_dyn_trait_metadata() -> usize {
        let c = FixedCounter;
        let dyn_ref: &dyn Counter = &c;
        std::ptr::metadata(dyn_ref).size_of()
    }
"#;

const CUSTOM_DST_UNSIZE_METADATA_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub struct Wrapper<T: ?Sized> {
        header: u8,
        data: T,
    }

    pub fn probe_custom_dst_unsize_metadata(w: &Wrapper<[u8; 3]>) -> usize {
        let wide: &Wrapper<[u8]> = w;
        std::ptr::metadata(wide)
    }
"#;

fn ptr_metadata_operand_for_entry(body: &Body, entry: &str) -> (Operand, usize) {
    for block in &body.blocks {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
            continue;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            continue;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
            continue;
        };
        let name = def.trimmed_name();
        if !(name == "metadata" || name.ends_with("::metadata")) {
            continue;
        }
        let operand = args.first().cloned().expect("ptr::metadata should have one argument");
        let local = operand_local(&operand, entry);
        return (operand, local);
    }
    panic!("expected std::ptr::metadata call in {entry} MIR");
}

fn operand_local(operand: &Operand, entry: &str) -> usize {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        other => panic!("expected Copy/Move operand for {entry}, got {other:?}"),
    }
}

fn trace_metadata_source_local(body: &Body, start_local: usize) -> Option<usize> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                continue;
            };
            if lhs.local != start_local || !lhs.projection.is_empty() {
                continue;
            }
            return match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => Some(place.local),
                Rvalue::CopyForDeref(place) => Some(place.local),
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    if place.projection.is_empty()
                        || (place.projection.len() == 1
                            && matches!(
                                place.projection[0],
                                rustc_public::mir::ProjectionElem::Deref
                            )) =>
                {
                    Some(place.local)
                }
                Rvalue::Cast(_, src_operand, _) => match src_operand {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        Some(place.local)
                    }
                    _ => None,
                },
                _ => None,
            };
        }
    }
    None
}

fn find_custom_dst_unsize_dest_local(body: &Body, entry: &str) -> usize {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, _) =
                rhs
            {
                let (Operand::Copy(src) | Operand::Move(src)) = operand else {
                    continue;
                };
                if src.projection.is_empty() && lhs.projection.is_empty() {
                    return lhs.local;
                }
            }
        }
    }
    panic!("expected custom-DST PointerCoercion::Unsize in {entry} MIR");
}

fn with_ptr_metadata_ctx<F>(source: &str, entry: &str, check: F)
where
    F: FnOnce(&Body, &mut ChcCtx<'_, '_>, Operand, usize) + Send,
{
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, entry);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, entry, ChcConfig::default());
        chc_ctx.declare_block_relations();
        let (operand, dest_local) = ptr_metadata_operand_for_entry(&body, entry);
        check(&body, &mut chc_ctx, operand, dest_local);
    });
}

fn assert_ptr_metadata_const(expr: &Expr, expected: u64) {
    match expr.value() {
        ExprValue::BitVecConst { value, width } => {
            assert_eq!(*width, crate::codegen_ay::types::POINTER_WIDTH);
            assert_eq!(
                u64::try_from(value).ok(),
                Some(expected),
                "expected PtrMetadata bitvec const {expected}, got {expr}"
            );
        }
        other => panic!("expected PtrMetadata bitvec const {expected}, got {other:?}"),
    }
}

fn assert_ptr_metadata_var_named(expr: &Expr, expected: &str) {
    assert!(
        matches!(expr.value(), ExprValue::Var { name } if name == expected),
        "expected PtrMetadata var {expected}, got {expr}"
    );
}

fn assert_ptr_metadata_dynamic_subslice_len(expr: &Expr, inclusive: bool) {
    fn is_var_expr(expr: &Expr) -> bool {
        matches!(expr.value(), ExprValue::Var { .. })
    }

    match expr.value() {
        ExprValue::BvSub(lhs, rhs) if !inclusive => {
            assert!(is_var_expr(lhs), "expected dynamic upper-bound var in {expr}");
            assert!(is_var_expr(rhs), "expected dynamic lower-bound var in {expr}");
        }
        ExprValue::BvAdd(sum, one) if inclusive => {
            assert!(
                matches!(one.value(), ExprValue::BitVecConst { value, width }
                    if *width == crate::codegen_ay::types::POINTER_WIDTH
                        && u64::try_from(value).ok() == Some(1)),
                "expected inclusive length to add bv1 in {expr}"
            );
            match sum.value() {
                ExprValue::BvSub(lhs, rhs) => {
                    assert!(is_var_expr(lhs), "expected dynamic upper-bound var in {expr}");
                    assert!(is_var_expr(rhs), "expected dynamic lower-bound var in {expr}");
                }
                other => panic!("expected inclusive length to wrap a BvSub, got {other:?}"),
            }
        }
        other => panic!("expected dynamic subslice length expression, got {other:?}"),
    }
}

fn assert_ptr_metadata_fallback_var(expr: &Expr) {
    assert!(
        matches!(expr.value(), ExprValue::Var { name } if name.starts_with("ptr_metadata_")),
        "expected fresh ptr_metadata_* fallback var, got {expr}"
    );
}

fn body_has_range_call_result(body: &Body, dest_local: usize, inclusive: bool) -> bool {
    body.blocks.iter().any(|block| {
        let TerminatorKind::Call { args, destination, .. } = &block.terminator.kind else {
            return false;
        };
        if destination.local != dest_local {
            return false;
        }
        args.iter().any(|arg| {
            let Ok(ty) = arg.ty(body.locals()) else {
                return false;
            };
            matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.trimmed_name() == if inclusive { "RangeInclusive" } else { "Range" }
            )
        })
    })
}

#[test]
fn test_ptr_metadata_thin_pointer_returns_zero() {
    for entry in ["probe_thin_ref_metadata", "probe_thin_raw_metadata", "probe_thin_fn_metadata"] {
        with_ptr_metadata_ctx(THIN_PTR_SOURCE, entry, |body, chc_ctx, _operand, metadata_local| {
            let source_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(source_local.into());
            let before = chc_ctx.diagnostics.ptr_metadata_unconstrained.get();
            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("thin pointer metadata should translate");
            let after = chc_ctx.diagnostics.ptr_metadata_unconstrained.get();

            assert_ptr_metadata_const(&expr, 0);
            assert_eq!(after, before, "{entry} should not increment ptr_metadata_unconstrained");
        });
    }
}

#[test]
fn test_ptr_metadata_unresolved_wide_pointer_increments_counter() {
    with_ptr_metadata_ctx(
        UNRESOLVED_WIDE_SOURCE,
        "probe_unresolved_slice_metadata",
        |body, chc_ctx, _operand, metadata_local| {
            let source_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(source_local.into());
            chc_ctx.ref_resolution.subslice_len.clear();
            chc_ctx.ref_resolution.slice_to_vec_local.clear();
            chc_ctx.dyn_vtable_ids.clear();
            chc_ctx.vtable_state_vars.clear();
            chc_ctx.collections.len_state.len_var_names.clear();

            let before = chc_ctx.diagnostics.ptr_metadata_unconstrained.get();
            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("wide pointer metadata should resolve");
            let after = chc_ctx.diagnostics.ptr_metadata_unconstrained.get();

            // Part of #4163: Two concrete resolution paths now exist before the
            // unconstrained fallback:
            // 1. Flattened fld1 extraction (for 2-field flattened fat pointers)
            // 2. BV128 high-bits extraction (for non-flattened BV128 fat pointers)
            // When either fires, the counter should NOT increment.
            if after == before {
                // Concrete resolution fired (flattened fld1 or BV128 extraction).
                // The expr should NOT be a ptr_metadata_* symbolic.
                assert!(
                    !matches!(expr.value(), ExprValue::Var { name } if name.starts_with("ptr_metadata_")),
                    "counter unchanged but got unconstrained symbolic"
                );
            } else {
                assert_ptr_metadata_fallback_var(&expr);
                assert_eq!(
                    after,
                    before + 1,
                    "unresolved wide PtrMetadata should increment the counter once"
                );
            }
        },
    );
}

#[test]
fn test_ptr_metadata_subslice_range_prefers_dynamic_len_over_array_extent() {
    with_ptr_metadata_ctx(
        SUBSLICE_RANGE_SOURCE,
        "probe_subslice_range_metadata",
        |body, chc_ctx, _operand, metadata_local| {
            let source_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(source_local.into());
            assert_mir_pattern_found(
                body_has_range_call_result(body, source_local, false),
                "Range call result feeding PtrMetadata",
            );
            chc_ctx.ref_resolution.subslice_len.clear();

            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("range subslice metadata should recover dynamic len");

            assert_ptr_metadata_dynamic_subslice_len(&expr, false);
            assert_eq!(
                chc_ctx.diagnostics.ptr_metadata_unconstrained.get(),
                0,
                "Range subslice should not hit ptr_metadata_* fallback"
            );
        },
    );
}

#[test]
fn test_ptr_metadata_subslice_range_inclusive_adds_one() {
    with_ptr_metadata_ctx(
        SUBSLICE_RANGE_INCLUSIVE_SOURCE,
        "probe_subslice_range_inclusive_metadata",
        |body, chc_ctx, _operand, metadata_local| {
            let source_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(source_local.into());
            assert_mir_pattern_found(
                body_has_range_call_result(body, source_local, true),
                "RangeInclusive call result feeding PtrMetadata",
            );
            chc_ctx.ref_resolution.subslice_len.clear();

            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("range-inclusive subslice metadata should recover dynamic len");

            assert_ptr_metadata_dynamic_subslice_len(&expr, true);
            assert_eq!(
                chc_ctx.diagnostics.ptr_metadata_unconstrained.get(),
                0,
                "RangeInclusive subslice should not hit ptr_metadata_* fallback"
            );
        },
    );
}

#[test]
fn test_ptr_metadata_boxed_str_raw_ptr_uses_len_state_trace() {
    with_ptr_metadata_ctx(
        BOXED_STR_METADATA_SOURCE,
        "probe_boxed_str_metadata",
        |_body, chc_ctx, operand, _metadata_local| {
            let raw_local = operand_local(&operand, "probe_boxed_str_metadata");
            let known_len_vars: Vec<_> =
                chc_ctx.collections.len_state.len_var_names.values().cloned().collect();
            assert!(
                !known_len_vars.is_empty(),
                "boxed str probe should seed tracked len vars before PtrMetadata translation"
            );
            assert!(
                chc_ctx.collections.len_state.get_len_var(raw_local).is_none(),
                "boxed str raw *const str local should force the MIR-trace path, not direct len lookup"
            );

            let expr = chc_ctx
                .translate_ptr_metadata(&operand, &HashSet::new())
                .expect("boxed str raw pointer metadata should resolve through MIR trace");

            match expr.value() {
                ExprValue::Var { name } => {
                    assert!(
                        known_len_vars.iter().any(|tracked| tracked.as_ref() == name),
                        "boxed str PtrMetadata should reuse a tracked len var, got {name}; known vars={known_len_vars:?}"
                    );
                    assert!(
                        !name.starts_with("ptr_metadata_"),
                        "boxed str PtrMetadata should not fall back to a fresh symbolic var"
                    );
                }
                ExprValue::BitVecConst { value, width }
                    if *width == crate::codegen_ay::types::POINTER_WIDTH
                        && u64::try_from(value).ok() == Some(5) => {}
                other => panic!("expected tracked len var for boxed str metadata, got {other:?}"),
            }
            assert_eq!(
                chc_ctx.diagnostics.ptr_metadata_unconstrained.get(),
                0,
                "boxed str PtrMetadata should not increment ptr_metadata_unconstrained"
            );
        },
    );
}

#[test]
fn test_ptr_metadata_vec_backed_tuple_wrapper_uses_struct_embedded_len() {
    with_ptr_metadata_ctx(
        TUPLE_WRAPPER_METADATA_SOURCE,
        "probe_clause_metadata",
        |body, chc_ctx, _operand, metadata_local| {
            let slice_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(slice_local.into());

            // In production, VecAsSlice call translation seeds slice_to_vec_local.
            // Since with_ptr_metadata_ctx only creates ChcCtx + declare_block_relations
            // (no call translation), we seed the mapping manually to test the
            // translate_ptr_metadata resolution path in isolation.
            //
            // Use local 1 as the wrapper (CnfClause) — the first user local in the
            // probe function, which wraps the Vec<i32>.
            let wrapper_local = 1;
            let len_var_name: Arc<str> = Arc::from("len_clause_vec");
            chc_ctx.ref_resolution.slice_to_vec_local.insert(slice_local, wrapper_local);
            chc_ctx.collections.len_state.len_var_names.insert(wrapper_local, len_var_name.clone());

            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("tuple-wrapper slice metadata should resolve through slice_to_vec_local");

            assert_ptr_metadata_var_named(&expr, &len_var_name);
            assert_eq!(
                chc_ctx.diagnostics.ptr_metadata_unconstrained.get(),
                0,
                "tuple-wrapper Vec metadata should not increment ptr_metadata_unconstrained"
            );
        },
    );
}

#[test]
fn test_ptr_metadata_dyn_trait_prefers_dyn_vtable_ids() {
    with_ptr_metadata_ctx(
        DYN_METADATA_SOURCE,
        "probe_dyn_trait_metadata",
        |body, chc_ctx, _operand, metadata_local| {
            let dyn_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(dyn_local.into());
            let expected = Expr::bitvec_const(7, crate::codegen_ay::types::POINTER_WIDTH);

            chc_ctx
                .vtable_state_vars
                .insert(dyn_local, (Arc::from("dyn_vtable_in"), Arc::from("dyn_vtable_out")));
            chc_ctx.dyn_vtable_ids.insert(dyn_local, expected.clone());

            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("dyn PtrMetadata should resolve through dyn_vtable_ids");

            assert_eq!(
                expr.to_string(),
                expected.to_string(),
                "dyn_vtable_ids should win over path-sensitive state vars when both exist"
            );
            assert_eq!(
                chc_ctx.diagnostics.ptr_metadata_unconstrained.get(),
                0,
                "dyn_vtable_ids resolution should avoid symbolic ptr_metadata fallback"
            );
        },
    );
}

#[test]
fn test_ptr_metadata_dyn_trait_uses_input_state_var_when_path_sensitive() {
    with_ptr_metadata_ctx(
        DYN_METADATA_SOURCE,
        "probe_dyn_trait_metadata",
        |body, chc_ctx, _operand, metadata_local| {
            let dyn_local =
                trace_metadata_source_local(body, metadata_local).unwrap_or(metadata_local);
            let source_operand = Operand::Copy(dyn_local.into());
            let in_name: Arc<str> = Arc::from("ptr_metadata_dyn_vtable_in");
            let out_name: Arc<str> = Arc::from("ptr_metadata_dyn_vtable_out");

            chc_ctx.dyn_vtable_ids.remove(&dyn_local);
            chc_ctx.vtable_state_vars.insert(dyn_local, (in_name.clone(), out_name));

            let expr = chc_ctx
                .translate_ptr_metadata(&source_operand, &HashSet::new())
                .expect("dyn PtrMetadata should resolve through vtable_state_vars");

            assert_ptr_metadata_var_named(&expr, &in_name);
            assert_eq!(
                expr.sort().bitvec_width(),
                Some(crate::codegen_ay::types::POINTER_WIDTH),
                "path-sensitive dyn PtrMetadata should stay at pointer-width sort: {:?}",
                expr.sort()
            );
            assert_eq!(
                chc_ctx.diagnostics.ptr_metadata_unconstrained.get(),
                0,
                "vtable state-var resolution should avoid symbolic ptr_metadata fallback"
            );
        },
    );
}

#[test]
fn test_ptr_metadata_custom_dst_unsize_destination_uses_subslice_len_side_table() {
    with_test_ay_ctx_for_source(CUSTOM_DST_UNSIZE_METADATA_SOURCE, |ctx| {
        let entry = "probe_custom_dst_unsize_metadata";
        let instance = find_instance_by_suffix(ctx.tcx, entry);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, entry, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = find_custom_dst_unsize_dest_local(&body, entry);
        let operand = Operand::Copy(dest_local.into());
        let seeded_len = Expr::var("custom_dst_unsize_len", crate::codegen_ay::types::ptr_sort());
        chc_ctx.ref_resolution.subslice_len.insert(dest_local, seeded_len.clone());

        let before = chc_ctx.diagnostics.ptr_metadata_unconstrained.get();
        let expr = chc_ctx
            .translate_ptr_metadata(&operand, &HashSet::new())
            .expect("custom-DST Unsize destination metadata should resolve from subslice_len");
        let after = chc_ctx.diagnostics.ptr_metadata_unconstrained.get();

        assert_eq!(
            expr.to_string(),
            seeded_len.to_string(),
            "custom-DST Unsize destination should resolve PtrMetadata from the seeded subslice_len side table"
        );
        assert_eq!(
            after, before,
            "custom-DST Unsize destination should not increment ptr_metadata_unconstrained"
        );
        assert!(
            !matches!(expr.value(), ExprValue::Var { name } if name.starts_with("ptr_metadata_")),
            "custom-DST Unsize destination should not fall back to a fresh ptr_metadata_* symbolic: {expr}"
        );
    });
}

// ---------- Part of #3978: Rc<dyn> raw-parts isolation regression ----------
//
// The compiletest harnesses `check_rc_dyn_raw_parts` and `check_rc_dyn_diff_raw_parts`
// still include a custom-`Drop` tail on the inner `Table`. These isolation probes
// neutralize that cleanup path with `core::mem::forget()` so the tests can focus on
// whether `Rc::as_ptr(...).to_raw_parts()` stays on the precise CHC lane.

const RC_DYN_RAW_PARTS_CLONE_ISOLATED_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    use std::rc::Rc;

    trait Furniture {
        fn cost(&self) -> i16;
    }

    struct Table {
        fancy: bool,
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    pub fn probe_rc_dyn_raw_parts_clone_isolated(fancy: bool) {
        let table: Rc<dyn Furniture> = Rc::new(Table { fancy });
        let cloned = table.clone();

        let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
        let (clone_ptr, clone_vtable) = Rc::as_ptr(&cloned).to_raw_parts();
        assert!(table_ptr == clone_ptr);
        assert!(table_vtable == clone_vtable);

        core::mem::forget(table);
        core::mem::forget(cloned);
    }
"#;

const RC_DYN_RAW_PARTS_DIFF_ISOLATED_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    use std::rc::Rc;

    trait Furniture {
        fn cost(&self) -> i16;
    }

    struct Table {
        fancy: bool,
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    pub fn probe_rc_dyn_raw_parts_diff_isolated(a: bool, b: bool) {
        let t1: Rc<dyn Furniture> = Rc::new(Table { fancy: a });
        let t2: Rc<dyn Furniture> = Rc::new(Table { fancy: b });

        let (_t1_ptr, t1_vtable) = Rc::as_ptr(&t1).to_raw_parts();
        let (_t2_ptr, t2_vtable) = Rc::as_ptr(&t2).to_raw_parts();
        // Both Rc<dyn Furniture> values are backed by the same concrete type,
        // so their vtable pointers must be equal.
        assert!(t1_vtable == t2_vtable);

        core::mem::forget(t1);
        core::mem::forget(t2);
    }
"#;

const RC_DYN_FULL_SHAPE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }

        fn new_furniture(fancy: bool) -> Rc<dyn Furniture> {
            Rc::new(Table::new(fancy))
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn check_rc_dyn_raw_parts(flag: bool) {
        let table = Table::new_furniture(flag);
        let furniture = table.clone();

        let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
        let (furn_ptr, furn_vtable) = Rc::as_ptr(&furniture).to_raw_parts();
        assert!(table_ptr == furn_ptr);
        assert!(table_vtable == furn_vtable);
    }

    pub fn check_rc_dyn_diff_raw_parts(a: bool, b: bool) {
        let table = Table::new_furniture(a);
        let furniture = Table::new_furniture(b);

        let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
        let (furn_ptr, furn_vtable) = Rc::as_ptr(&furniture).to_raw_parts();
        assert!(table_ptr != furn_ptr);
        assert!(table_vtable == furn_vtable);
    }
"#;

/// Part of #3978: isolation regression — cloned `Rc<dyn>` raw-parts share the
/// same data pointer and vtable when the drop tail is neutralized via `forget`.
///
/// Part of #4004: the isolated clone path must avoid `P_inf_*` summaries for
/// raw-pointer `to_raw_parts()` and stay solver-clean.
#[test]
fn test_rc_dyn_raw_parts_clone_isolated_vc_is_well_formed() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(RC_DYN_RAW_PARTS_CLONE_ISOLATED_SOURCE, |ctx| {
        let fn_name = "probe_rc_dyn_raw_parts_clone_isolated";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.starts_with("P_inf_"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should keep raw-parts decomposition precise instead of emitting inferable summaries: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should not record CHC fallback after raw-parts dispatch recovery"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });

    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    assert_eq!(
        inferable_count, 0,
        "probe_rc_dyn_raw_parts_clone_isolated should keep inferable_predicate at zero"
    );
}

/// Part of #3978: isolation regression — separately-allocated `Rc<dyn>` values
/// have the same vtable when both back the same concrete type.
///
/// Part of #4004: this diff-allocation lane must avoid `P_inf_*` summaries for
/// raw-pointer `to_raw_parts()` and stay solver-clean.
#[test]
fn test_rc_dyn_raw_parts_diff_isolated_vc_is_well_formed() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(RC_DYN_RAW_PARTS_DIFF_ISOLATED_SOURCE, |ctx| {
        let fn_name = "probe_rc_dyn_raw_parts_diff_isolated";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.starts_with("P_inf_"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should keep raw-parts decomposition precise instead of emitting inferable summaries: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should not record CHC fallback after raw-parts dispatch recovery"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });

    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    assert_eq!(
        inferable_count, 0,
        "probe_rc_dyn_raw_parts_diff_isolated should keep inferable_predicate at zero"
    );
}

fn inferable_decl_names_for_probe_with_config(
    source: &str,
    fn_name: &str,
    config: ChcConfig,
) -> Vec<String> {
    let mut inferable = Vec::new();
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, config);

        inferable = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();
    });
    inferable
}

fn inferable_decl_names_for_probe(source: &str, fn_name: &str) -> Vec<String> {
    inferable_decl_names_for_probe_with_config(source, fn_name, ChcConfig::default())
}

#[test]
fn test_rc_dyn_raw_parts_clone_isolated_reports_live_inferable_paths() {
    let inferable = inferable_decl_names_for_probe(
        RC_DYN_RAW_PARTS_CLONE_ISOLATED_SOURCE,
        "probe_rc_dyn_raw_parts_clone_isolated",
    );

    assert!(
        inferable.is_empty(),
        "clone-isolated raw-parts probe should not emit inferable summaries after #4004: {inferable:?}"
    );
}

#[test]
fn test_rc_dyn_raw_parts_diff_isolated_reports_live_inferable_paths() {
    let inferable = inferable_decl_names_for_probe(
        RC_DYN_RAW_PARTS_DIFF_ISOLATED_SOURCE,
        "probe_rc_dyn_raw_parts_diff_isolated",
    );

    assert!(
        inferable.is_empty(),
        "diff-isolated raw-parts probe should not emit inferable summaries after #4004: {inferable:?}"
    );
}

#[test]
fn test_rc_dyn_compiletest_raw_parts_reports_live_inferable_paths() {
    let raw_parts =
        inferable_decl_names_for_probe(RC_DYN_FULL_SHAPE_SOURCE, "check_rc_dyn_raw_parts");
    let diff_raw_parts =
        inferable_decl_names_for_probe(RC_DYN_FULL_SHAPE_SOURCE, "check_rc_dyn_diff_raw_parts");

    assert!(
        raw_parts.is_empty() && diff_raw_parts.is_empty(),
        "compiletest-shaped rc_dyn raw-parts probes should stay solver-clean after #4004: raw={raw_parts:?}, diff={diff_raw_parts:?}"
    );
}

#[test]
fn test_dyn_trait_metadata_size_of_avoids_inferable_summaries() {
    let inferable = inferable_decl_names_for_probe(DYN_METADATA_SOURCE, "probe_dyn_trait_metadata");

    assert!(
        inferable.is_empty(),
        "dyn metadata size_of probe should not emit inferable summaries: {inferable:?}"
    );
}
