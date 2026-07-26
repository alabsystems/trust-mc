// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for the `codegen_call_dispatch_misc` module.
//!
//! Part of #2303: dedicated misc-dispatch coverage.
//! Covers dispatch paths exercised by `try_dispatch_call_misc`:
//! - `detect_mem_intrinsic_stub` → size_of / align_of
//! - `detect_primitive_clone_stub` → Clone::clone for Copy types
//! - `detect_raw_eq_call` → intrinsics::raw_eq
//! - `detect_rawvec_stub` → RawVec internals
//! - `detect_ptr_cast_stub` → pointer casts
//! - `detect_display_cow_stub` → Display/Cow toString
//! - `detect_iterator_adapter_stub` → iterator adapters
//! - `detect_primitive_cmp_stub` → PartialEq/PartialOrd trait stubs
//!
//! Tests exercise the dispatch path:
//!   mir_to_chc → generate_transition_rules → codegen_call_terminator → try_dispatch_call_misc

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::common::*;
use ay_bindings::Expr;
use trust_mc_core::decl::Decl;

const POSIX_MEMALIGN_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(rustc_private)]

    extern crate libc;
    use core::ptr;

    pub unsafe fn probe_posix_memalign_dispatch(alignment: usize) -> i32 {
        let mut out = ptr::null_mut();
        unsafe { libc::posix_memalign(&mut out, alignment, 4) }
    }
"#;

const POSIX_MEMALIGN_INVALID_CONST_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(rustc_private)]

    extern crate libc;
    use core::ptr;

    pub unsafe fn probe_posix_memalign_invalid_const() -> i32 {
        let mut out = ptr::null_mut();
        unsafe { libc::posix_memalign(&mut out, 1, 4) }
    }
"#;

const SYSCONF_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(rustc_private)]

    extern crate libc;

    pub unsafe fn probe_sysconf_dispatch() -> libc::c_long {
        unsafe { libc::sysconf(libc::_SC_PAGESIZE) }
    }
"#;

// =============================================================================
// mem::size_of / mem::align_of — detect_mem_intrinsic_stub
// =============================================================================

const SIZE_OF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_size_of() -> usize {
        core::mem::size_of::<u32>()
    }
"#;

/// size_of::<T> should be dispatched through try_dispatch_call_misc.
#[test]
fn test_size_of_generates_vc() {
    with_test_ay_ctx_for_source(SIZE_OF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_size_of", ChcConfig::default());

        assert_vc_structure(&vc, "probe_size_of", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_size_of",
            ay_bindings::Sort::is_bitvec,
            "bitvector",
        );
        assert_has_nontrivial_transition_constraints(&vc, "probe_size_of");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_size_of",
            |e| matches!(e.value(), ExprValue::BitVecConst { .. }),
            "BitVecConst",
        );
    });
}

/// size_of should detect the mem intrinsic stub.
#[test]
fn test_size_of_detects_mem_intrinsic() {
    with_test_ay_ctx_for_source(SIZE_OF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_size_of", ChcConfig::default());

        let stubs = collect_detected_mem_intrinsic_stubs(&chc_ctx, &body);
        assert!(!stubs.is_empty(), "size_of should be detected as mem intrinsic stub");
    });
}

const ALIGN_OF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_align_of() -> usize {
        core::mem::align_of::<u64>()
    }
"#;

/// align_of::<T> should also be dispatched as mem intrinsic.
#[test]
fn test_align_of_generates_vc() {
    with_test_ay_ctx_for_source(ALIGN_OF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_align_of");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_align_of", ChcConfig::default());

        assert_vc_structure(&vc, "probe_align_of", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_align_of",
            ay_bindings::Sort::is_bitvec,
            "bitvector",
        );
        assert_has_nontrivial_transition_constraints(&vc, "probe_align_of");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_align_of",
            |e| matches!(e.value(), ExprValue::BitVecConst { .. }),
            "BitVecConst",
        );
    });
}

#[test]
fn test_posix_memalign_dispatch_splits_invalid_and_success_rules() {
    with_test_ay_ctx_for_source(POSIX_MEMALIGN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_posix_memalign_dispatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_posix_memalign_dispatch", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found_call = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if path != "libc::posix_memalign" {
                continue;
            }
            found_call = true;

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = *target;
            let callee_path = chc_ctx.resolve_callee_path(func);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path,
            };

            assert!(chc_ctx.codegen_call_terminator(&dcx), "posix_memalign should dispatch");
            assert_eq!(chc_ctx.vc.rules.len(), 2, "should split into invalid+success rules");
            assert!(!chc_ctx.vc.rules.iter().any(|r| r.head.name == "error"), "no error rule");
            assert!(vc_rules_contain_var(&chc_ctx.vc, "obj_valid__out"), "uses heap allocator");
            let has_einval = chc_ctx.vc.rules.iter().any(|rule| {
                rule_contains_expr(rule, |expr| {
                    matches!(expr.value(), ExprValue::BitVecConst { value, width }
                        if *width == 32 && u64::try_from(value).ok() == Some(22))
                })
            });
            assert!(has_einval, "invalid branch should return EINVAL=22");
            break;
        }

        assert!(found_call, "expected direct libc::posix_memalign call in MIR");
    });
}

#[test]
fn test_posix_memalign_invalid_const_emits_only_einval_rule() {
    with_test_ay_ctx_for_source(POSIX_MEMALIGN_INVALID_CONST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_posix_memalign_invalid_const");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_posix_memalign_invalid_const", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found_call = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            if chc_ctx.resolve_callee_path(func).as_deref() != Some("libc::posix_memalign") {
                continue;
            }
            found_call = true;

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = *target;
            let callee_path = chc_ctx.resolve_callee_path(func);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path,
            };

            assert!(chc_ctx.codegen_call_terminator(&dcx), "posix_memalign should dispatch");
            assert_eq!(chc_ctx.vc.rules.len(), 1, "invalid constant alignment needs one rule");
            assert!(!chc_ctx.vc.rules.iter().any(|r| r.head.name == "error"), "no error rule");
            assert!(chc_ctx.vc.rules.iter().any(|rule| {
                rule_contains_expr(rule, |expr| {
                    matches!(expr.value(), ExprValue::BitVecConst { value, width }
                        if *width == 32 && u64::try_from(value).ok() == Some(22))
                })
            }));
            assert!(!chc_ctx.vc.rules.iter().any(|rule| {
                rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::Var { name }
                            if name == "obj_valid__out" || name == "obj_size__out")
                    })
                })
            }));
            break;
        }

        assert!(found_call, "expected direct libc::posix_memalign call in MIR");
    });
}

#[test]
fn test_sysconf_dispatch_havocs_return_without_error_rule() {
    with_test_ay_ctx_for_source(SYSCONF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_sysconf_dispatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_sysconf_dispatch", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found_call = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if path != "libc::sysconf" {
                continue;
            }
            found_call = true;

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = *target;
            let callee_path = chc_ctx.resolve_callee_path(func);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path,
            };

            assert!(chc_ctx.codegen_call_terminator(&dcx), "sysconf should dispatch");
            assert_eq!(chc_ctx.vc.rules.len(), 1, "sysconf should emit one normal goto rule");
            assert!(!chc_ctx.vc.rules.iter().any(|r| r.head.name == "error"), "no error rule");

            let inferable_decls: Vec<_> = chc_ctx
                .vc
                .decls
                .iter()
                .filter_map(|decl| match decl {
                    Decl::Fun { name, .. } if name.contains("libc::sysconf") => {
                        Some(name.to_string())
                    }
                    _ => None,
                })
                .collect();
            assert!(
                inferable_decls.is_empty(),
                "sysconf should not use P_inf_* inferable summaries: {inferable_decls:?}"
            );
            break;
        }

        assert!(found_call, "expected direct libc::sysconf call in MIR");
    });
}

// =============================================================================
// Clone::clone for Copy types — detect_primitive_clone_stub
// =============================================================================

const CLONE_COPY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_clone_copy(x: u32) -> u32 {
        x.clone()
    }
"#;

/// Clone::clone on a Copy type should be dispatched as identity (Copy semantics).
#[test]
fn test_clone_copy_generates_vc() {
    with_test_ay_ctx_for_source(CLONE_COPY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_clone_copy");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_clone_copy", ChcConfig::default());

        assert_vc_structure(&vc, "probe_clone_copy", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_clone_copy",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

// =============================================================================
// PartialEq / PartialOrd trait stubs — detect_primitive_cmp_stub
// =============================================================================

const PARTIAL_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_partial_eq(a: u32, b: u32) -> bool {
        a == b
    }
"#;

/// PartialEq::eq on primitives should be dispatched through detect_primitive_cmp_stub.
#[test]
fn test_partial_eq_generates_vc() {
    with_test_ay_ctx_for_source(PARTIAL_EQ_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_partial_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_partial_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_partial_eq", body.blocks.len());
        assert_relation_has_arg_sort(&vc, "probe_partial_eq", ay_bindings::Sort::is_bool, "Bool");
    });
}

const PARTIAL_ORD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_partial_ord(a: u32, b: u32) -> bool {
        a < b
    }
"#;

/// PartialOrd::lt on primitives should be dispatched through detect_primitive_cmp_stub.
#[test]
fn test_partial_ord_generates_vc() {
    with_test_ay_ctx_for_source(PARTIAL_ORD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_partial_ord");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_partial_ord", ChcConfig::default());

        assert_vc_structure(&vc, "probe_partial_ord", body.blocks.len());
        assert_relation_has_arg_sort(&vc, "probe_partial_ord", ay_bindings::Sort::is_bool, "Bool");
    });
}

// =============================================================================
// Iterator adapters — detect_iterator_adapter_stub
// =============================================================================

const ITER_MAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_iter_map() -> Vec<u32> {
        let v = vec![1u32, 2, 3];
        v.into_iter().map(|x| x + 1).collect()
    }
"#;

/// Iterator adapter (.map().collect()) should be dispatched through
/// detect_iterator_adapter_stub.
#[test]
fn test_iter_map_collect_generates_vc() {
    with_test_ay_ctx_for_source(ITER_MAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_map");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_iter_map", ChcConfig::default());

        assert_vc_structure(&vc, "probe_iter_map", body.blocks.len());
        // After recursive flattening (#2989), iterator adapter types
        // (Map<IntoIter<u32>>) are flattened to scalar state vars.
        // Verify that non-trivial scalar state vars exist.
        assert_relation_has_arg_sort(&vc, "probe_iter_map", ay_bindings::Sort::is_bitvec, "BitVec");
    });
}

const ITER_FILTER_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_iter_filter() -> Vec<u32> {
        let v = vec![1u32, 2, 3, 4];
        v.into_iter().filter(|x| *x > 2).collect()
    }
"#;

/// Iterator filter+collect exercises the adapter dispatch path.
#[test]
fn test_iter_filter_collect_generates_vc() {
    with_test_ay_ctx_for_source(ITER_FILTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_filter");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_iter_filter", ChcConfig::default());

        assert_vc_structure(&vc, "probe_iter_filter", body.blocks.len());
        // After recursive flattening (#2989), iterator adapter types
        // (Filter<IntoIter<u32>>) are flattened to scalar state vars.
        assert_relation_has_arg_sort(
            &vc,
            "probe_iter_filter",
            ay_bindings::Sort::is_bitvec,
            "BitVec",
        );
    });
}

// Range-len tests moved to test_call_dispatch_misc_range_len.rs (D4 of #4010).

// =============================================================================
// Pointer cast — detect_ptr_cast_stub
// =============================================================================

const PTR_CAST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ptr_cast(x: &u32) -> *const u32 {
        x as *const u32
    }
"#;

/// Pointer cast (&T → *const T) should be dispatched as identity.
#[test]
fn test_ptr_cast_generates_vc() {
    with_test_ay_ctx_for_source(PTR_CAST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_cast");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_cast", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ptr_cast", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_ptr_cast",
            ay_bindings::Sort::is_bitvec,
            "bitvector",
        );
    });
}

// test_ptr_cast_detects_stub was deleted in #2459.
// Reason: `&T as *const T` is an Rvalue::Cast in MIR, never a Call terminator.
// `core::ptr::from_ref` is also inlined to a cast at MIR level.
// The stub detection function only scans Call terminators, so this test was
// always vacuously passing. Pointer cast VC generation is still covered by
// test_ptr_cast_generates_vc above.

// =============================================================================
// Combined: size_of + comparison — exercises multiple dispatch paths
// =============================================================================

const COMBINED_SIZE_CMP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_combined_size_cmp() -> bool {
        core::mem::size_of::<u32>() == 4
    }
"#;

/// Combined size_of + eq exercises both mem intrinsic and cmp dispatch paths.
#[test]
fn test_combined_size_cmp_generates_vc() {
    with_test_ay_ctx_for_source(COMBINED_SIZE_CMP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_combined_size_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_combined_size_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_combined_size_cmp", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_combined_size_cmp",
            ay_bindings::Sort::is_bool,
            "Bool",
        );
    });
}
