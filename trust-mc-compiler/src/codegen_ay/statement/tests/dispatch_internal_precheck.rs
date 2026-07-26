// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for sound over-approximation btree/rawvec internal precheck branches.
//!
//! Part of #2529.

use super::*;

struct BtreeInternalPrecheckOutcome {
    callee_path: String,
    target: Option<rustc_public::mir::BasicBlockIdx>,
    handled: Option<Option<rustc_public::mir::BasicBlockIdx>>,
    assigned_expr: Option<Expr>,
}

fn run_btree_internal_precheck_for_call(
    source: &str,
    fn_suffix: &str,
    expected_path_fragment: &str,
) -> (Option<BtreeInternalPrecheckOutcome>, Vec<String>) {
    let mut outcome = None;
    let mut observed_paths = Vec::new();
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_suffix);
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        for bb in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &bb.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            observed_paths.push(callee_path.clone());
            if !callee_path.contains(expected_path_fragment) {
                continue;
            }
            let handled = codegen.try_codegen_btree_internal_precheck(
                func,
                &callee_path,
                args,
                destination,
                *target,
            );
            let dest_base = codegen.ssa_base_name(destination);
            let assigned_expr = codegen.env_lookup(&dest_base).cloned();
            outcome = Some(BtreeInternalPrecheckOutcome {
                callee_path,
                target: *target,
                handled,
                assigned_expr,
            });
            break;
        }
    });
    (outcome, observed_paths)
}

const BTREE_OPTION_AS_REF_PRECHECK_PROBE: &str = r#"
pub struct NodeRef;

pub fn option_as_ref_noderef(x: &Option<NodeRef>) -> Option<&NodeRef> {
    x.as_ref()
}
"#;

/// Regression for #2529 path #2: Option::as_ref with NodeRef generic should route
/// through internal precheck and assign a symbolic destination.
#[test]
fn test_mir_btree_internal_precheck_option_as_ref_assigns_symbolic() {
    let (outcome, observed_paths) = run_btree_internal_precheck_for_call(
        BTREE_OPTION_AS_REF_PRECHECK_PROBE,
        "option_as_ref_noderef",
        "as_ref",
    );
    let outcome = outcome.unwrap_or_else(|| {
        panic!("expected Option::as_ref call in MIR, observed paths: {observed_paths:?}")
    });

    assert!(
        outcome.callee_path.contains("Option") && outcome.callee_path.contains("as_ref"),
        "unexpected callee path: {}",
        outcome.callee_path
    );
    assert_eq!(
        outcome.handled,
        Some(outcome.target),
        "Option::as_ref<NodeRef> should be handled by btree internal precheck"
    );

    let assigned =
        outcome.assigned_expr.expect("precheck should assign symbolic result to destination");
    assert!(
        matches!(assigned.value(), ExprValue::Var { .. }),
        "expected symbolic var assignment, got {:?}",
        assigned.value()
    );
}

const BTREE_NODE_INTERNAL_PRECHECK_PROBE: &str = r#"
mod btree {
    pub mod node {
        #[inline(never)]
        pub fn internal_marker(v: bool) -> bool {
            !v
        }
    }
}

pub fn call_btree_internal_marker(v: bool) -> bool {
    btree::node::internal_marker(v)
}
"#;

/// Regression for #2529 path #3: btree::node internal calls should route through
/// the sound over-approximation symbolic fallback precheck.
#[test]
fn test_mir_btree_internal_precheck_node_path_assigns_symbolic() {
    let (outcome, observed_paths) = run_btree_internal_precheck_for_call(
        BTREE_NODE_INTERNAL_PRECHECK_PROBE,
        "call_btree_internal_marker",
        "btree::node::internal_marker",
    );
    let outcome = outcome.unwrap_or_else(|| {
        panic!("expected btree::node internal call in MIR, observed paths: {observed_paths:?}")
    });

    assert!(
        outcome.callee_path.contains("btree::node::"),
        "unexpected callee path: {}",
        outcome.callee_path
    );
    assert_eq!(
        outcome.handled,
        Some(outcome.target),
        "btree::node path should be handled by btree internal precheck"
    );

    let assigned =
        outcome.assigned_expr.expect("precheck should assign symbolic result to destination");
    assert!(
        matches!(assigned.value(), ExprValue::Var { .. }),
        "expected symbolic var assignment, got {:?}",
        assigned.value()
    );
}

const RAWVEC_INTERNAL_PRECHECK_PROBE: &str = r#"
mod raw_vec {
    pub struct RawVec;

    impl RawVec {
        #[inline(never)]
        pub fn allocate_in(&self) -> usize {
            1
        }
    }
}

pub fn call_rawvec_allocate_in() -> usize {
    let rv = raw_vec::RawVec;
    rv.allocate_in()
}
"#;

/// Regression for #2529 path #4: non-stub RawVec internal calls should route
/// through the sound over-approximation symbolic fallback precheck.
#[test]
fn test_mir_btree_internal_precheck_rawvec_nonstub_assigns_symbolic() {
    let (outcome, observed_paths) = run_btree_internal_precheck_for_call(
        RAWVEC_INTERNAL_PRECHECK_PROBE,
        "call_rawvec_allocate_in",
        "raw_vec::RawVec::allocate_in",
    );
    let outcome = outcome.unwrap_or_else(|| {
        panic!("expected RawVec::allocate_in call in MIR, observed paths: {observed_paths:?}")
    });

    assert!(
        outcome.callee_path.contains("raw_vec::RawVec::"),
        "unexpected callee path: {}",
        outcome.callee_path
    );
    assert_eq!(
        outcome.handled,
        Some(outcome.target),
        "RawVec non-stub path should be handled by btree internal precheck"
    );

    let assigned =
        outcome.assigned_expr.expect("precheck should assign symbolic result to destination");
    assert!(
        matches!(assigned.value(), ExprValue::Var { .. }),
        "expected symbolic var assignment, got {:?}",
        assigned.value()
    );
}
