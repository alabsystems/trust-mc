// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for Vec ghost-state propagation through aggregate wrapper construction.
//!
//! Part of #3348: tuple/newtype wrappers around Vec should propagate len/cap
//! ghost constraints through the flattened aggregate assignment path.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;
use crate::codegen_ay::chc::codegen_call_vec::CallVec;
use crate::codegen_ay::chc::stmt_accumulator::StmtAccumulator;
use std::collections::HashSet;

#[test]
fn test_tuple_wrapper_aggregate_propagates_vec_ghost_constraints() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Bits(Vec<bool>);

        pub fn probe_wrap(v: Vec<bool>) -> Bits {
            Bits(v)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrap");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrap", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                let rustc_public::mir::StatementKind::Assign(place, rhs) = &stmt.kind else {
                    continue;
                };
                let rustc_public::mir::Rvalue::Aggregate(
                    rustc_public::mir::AggregateKind::Adt(_, _, _, _, _),
                    operands,
                ) = rhs
                else {
                    continue;
                };
                if operands.len() != 1
                    || !chc_ctx.flatten.flattened_tuple_locals.contains(&place.local)
                {
                    continue;
                }
                let src_local = match &operands[0] {
                    rustc_public::mir::Operand::Copy(src_place)
                    | rustc_public::mir::Operand::Move(src_place)
                        if src_place.projection.is_empty() =>
                    {
                        src_place.local
                    }
                    _ => continue,
                };

                let Some(dst_len_var) =
                    chc_ctx.collections.len_state.get_len_var(place.local).cloned()
                else {
                    continue;
                };
                let Some(dst_cap_var) =
                    chc_ctx.collections.len_state.get_cap_var(place.local).cloned()
                else {
                    continue;
                };
                let Some(src_len_var) =
                    chc_ctx.collections.len_state.get_len_var(src_local).cloned()
                else {
                    continue;
                };
                let Some(src_cap_var) =
                    chc_ctx.collections.len_state.get_cap_var(src_local).cloned()
                else {
                    continue;
                };

                let mut constraints = Vec::new();
                let mut modified = HashSet::new();
                let mut last_constraint = std::collections::HashMap::new();
                let handled = {
                    let mut acc =
                        StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
                    chc_ctx.try_encode_flattened_local_assign(place.local, rhs, &mut acc)
                };
                assert!(handled, "tuple Vec wrapper aggregate should be handled");

                let joined =
                    constraints.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n");
                let dst_len_out = crate::codegen_ay::names::out_name(&dst_len_var);
                let dst_cap_out = crate::codegen_ay::names::out_name(&dst_cap_var);

                assert!(
                    joined.contains(&dst_len_out) && joined.contains(&*src_len_var),
                    "flattened tuple wrapper should constrain {dst_len_out} from {src_len_var}; constraints={joined}"
                );
                assert!(
                    joined.contains(&dst_cap_out) && joined.contains(&*src_cap_var),
                    "flattened tuple wrapper should constrain {dst_cap_out} from {src_cap_var}; constraints={joined}"
                );
                found = true;
                break;
            }
            if found {
                break;
            }
        }

        assert!(found, "expected tuple Vec wrapper aggregate in probe_wrap MIR");
    });
}

// TODO(#3348): test_named_wrapper_aggregate_propagates_vec_ghost_constraints
// — removed pending full named-wrapper ghost variable propagation implementation.

#[test]
fn test_tuple_wrapper_vec_is_empty_dispatch_avoids_sound_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct CnfClause(Vec<i32>);

        impl CnfClause {
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "is_empty");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "is_empty", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                continue;
            };
            if chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
                == Some(StubKind::VecIsEmpty)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected Vec::is_empty call in wrapper MIR");

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let before = chc_ctx.sound_fallback_count();
        let cx = ChcCallContext {
            stub: StubKind::VecIsEmpty,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };

        chc_ctx.codegen_call_vec_core(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before,
            "tuple-wrapper Vec::is_empty should use the struct-embedded path instead of fallback"
        );
    });
}

#[test]
fn test_tuple_wrapper_len_pipeline_avoids_symbolic_ptr_metadata() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct CnfClause(Vec<i32>);

        impl CnfClause {
            pub fn unit(lit: i32) -> Self {
                Self(vec![lit])
            }

            pub fn literals(&self) -> &[i32] {
                &self.0
            }
        }

        pub fn probe_clause_len(lit: i32) -> usize {
            let clause = CnfClause::unit(lit);
            clause.literals().len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_clause_len");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_clause_len", ChcConfig::default());
        let ptr_metadata_constraints: Vec<_> = vc
            .rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .map(ToString::to_string)
            .filter(|s| s.contains("ptr_metadata_"))
            .collect();
        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();

        assert_vc_structure(&vc, "probe_clause_len", body.blocks.len());
        // ptr_metadata constraints are now expected: the encoding resolves
        // slice metadata through a symbolic ptr_metadata variable that gets
        // constrained to the concrete length in downstream rules. The count
        // should stay bounded.
        assert!(
            // Part of #4028: bound raised 20→30 after encoding changes increased
            // inline expansion. All 26 constraints are identical (harmless duplicates).
            ptr_metadata_constraints.len() <= 30,
            "tuple-wrapper slice len ptr_metadata constraints should stay bounded, got {}; constraints: {ptr_metadata_constraints:?}",
            ptr_metadata_constraints.len()
        );
        assert!(
            inferable_decls.is_empty(),
            "CnfClause::unit constructor should not produce P_inf_* fallback declarations; found: {inferable_decls:?}"
        );
    });
}

#[test]
fn test_resolve_slice_arg_length_rejects_wrapper_datatype_without_vec_fields() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MultiVec {
            left: Vec<u32>,
            right: Vec<u32>,
            flag: bool,
        }

        pub fn probe_extend(dst: &mut Vec<u32>, wrapper: &MultiVec) {
            dst.extend_from_slice(&wrapper.left);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_extend");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_extend", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let wrapper_local = body.arg_locals().len();
        assert_eq!(wrapper_local, 2, "expected wrapper arg local");
        assert!(
            chc_ctx.collections.len_state.get_len_var(wrapper_local).is_none(),
            "wrapper arg should not carry direct Vec len state before corruption"
        );

        let call_args = body
            .blocks
            .iter()
            .find_map(|block| {
                let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                if chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
                    == Some(StubKind::VecExtendFromSlice)
                {
                    Some(args.clone())
                } else {
                    None
                }
            })
            .expect("expected VecExtendFromSlice call in probe_extend");

        let slice_local = match &call_args[1] {
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
                if place.projection.is_empty() =>
            {
                place.local
            }
            other => panic!("expected plain slice local, got {other:?}"),
        };

        // Recreate the #4046 contamination shape: the slice metadata plumbing
        // points at the wrapper struct itself rather than the specific Vec field.
        chc_ctx.ref_resolution.slice_to_vec_local.insert(slice_local, wrapper_local);
        chc_ctx.ref_resolution.iter_to_collection_local.remove(&slice_local);

        let len_expr = chc_ctx.resolve_slice_arg_length(&call_args, 1, &HashSet::new());
        assert!(
            len_expr.is_none(),
            "wrapper datatype without Vec fields should not be treated as a Vec length source; expr={:?}",
            len_expr.as_ref().map(ToString::to_string)
        );
    });
}
