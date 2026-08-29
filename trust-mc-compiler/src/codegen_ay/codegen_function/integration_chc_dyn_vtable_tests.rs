// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A dyn->dyn coercion must not bind its destination vtable state variable to
//! two DIFFERENT vtable ids in one rule.
//!
//! `apply_vtable_tracking` resolves `_d = _s as &dyn Any` (with
//! `_s: &(dyn Any + Send)`) to the TARGET trait's vtable id for the concrete
//! source type. `apply_late_vtable_propagation` then ran unconditionally and
//! copied `_s`'s SOURCE-trait id onto the same `__vtable_sv_N__out` variable.
//! The two ids differ, so the block asserted `1 == 0`, every path became
//! infeasible, and the harness verified VACUOUSLY with each check reported
//! UNREACHABLE — nothing proved, with only the driver's vacuity gate between
//! that and a clean "SUCCESSFUL".
//!
//! A plain `&T -> &dyn Trait` unsize never hit it: a non-dyn source has no
//! vtable state variable, so the late propagation found nothing to copy. It
//! took a source that was ITSELF a trait object, which is why the five
//! `tests/kani/DynTrait` rows that carried it all had a dyn->dyn cast.
//!
//! What is asserted is the CONTRADICTION, not the duplication: a rule may not
//! bind one `__vtable_sv_N__out` to two values that resolve to DIFFERENT
//! CONSTANTS. Duplicate bindings that agree, or that stay symbolic, are common
//! in the current encoding and are not what broke these harnesses — only the
//! disagreeing pair is unsatisfiable. (Making one binding per rule a hard
//! invariant would be the stronger guarantee; it needs last-write-wins applied
//! where a rule's constraint lists are MERGED, which is a separate change.)

#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue};

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

const DYN_TO_DYN_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::any::Any;

    pub fn probe_dyn_to_dyn(seed: i32) {
        let i: i32 = seed;
        let s: &(dyn Any + Send) = &i;
        // The trigger: a dyn->dyn cast that DROPS the `Send` auto trait.
        let c: &dyn Any = s as &dyn Any;
        let observed = match c.downcast_ref::<i32>() {
            Some(v) => *v,
            None => 0,
        };
        // A symbolic-trip-count loop keeps the straight-line enumeration from
        // discharging this body: it fails closed when a loop relation is not
        // fully reached. That leaves the block constraints intact WITHOUT
        // touching the process-global discharge-skip flag, which would perturb
        // every other test running concurrently.
        let mut acc = observed;
        let mut n = 0;
        while n < seed {
            acc = acc.wrapping_add(n);
            n += 1;
        }
        std::hint::black_box(acc);
    }
"#;

/// Every top-level `Eq` in the VC that pins a variable to a bitvector
/// constant, as `var name -> constant`. A name bound to two different
/// constants anywhere is dropped: it is not a reliable resolution.
fn constant_env(vc: &trust_mc_core::chc::ChcVc) -> HashMap<String, String> {
    let mut env: HashMap<String, String> = HashMap::new();
    let mut conflicted: Vec<String> = Vec::new();
    for rule in &vc.rules {
        for c in rule.body.constraints.iter() {
            let ExprValue::Eq(lhs, rhs) = c.value() else { continue };
            for (var_side, val_side) in [(lhs, rhs), (rhs, lhs)] {
                let (ExprValue::Var { name }, ExprValue::BitVecConst { value, .. }) =
                    (var_side.value(), val_side.value())
                else {
                    continue;
                };
                match env.insert(name.to_string(), value.to_string()) {
                    Some(prev) if prev != value.to_string() => conflicted.push(name.to_string()),
                    _ => {}
                }
            }
        }
    }
    for name in conflicted {
        env.remove(&name);
    }
    env
}

/// Resolve a binding's right-hand side to a constant, following one level of
/// variable indirection through `env`.
fn resolve_const(expr: &Expr, env: &HashMap<String, String>) -> Option<String> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => Some(value.to_string()),
        ExprValue::Var { name } => env.get(&**name).cloned(),
        _ => None,
    }
}

/// Top-level `__vtable_sv_N__out = <expr>` bindings in one rule body, keyed by
/// out-var name.
fn vtable_out_bindings<'a>(
    constraints: impl IntoIterator<Item = &'a Expr>,
) -> HashMap<String, Vec<Expr>> {
    let mut found: HashMap<String, Vec<Expr>> = HashMap::new();
    for c in constraints {
        let ExprValue::Eq(lhs, rhs) = c.value() else { continue };
        for (var_side, val_side) in [(lhs, rhs), (rhs, lhs)] {
            if let ExprValue::Var { name } = var_side.value()
                && name.starts_with("__vtable_sv_")
                && name.ends_with("__out")
            {
                found.entry(name.to_string()).or_default().push(val_side.clone());
            }
        }
    }
    found
}

#[test]
fn test_dyn_to_dyn_coercion_binds_vtable_out_var_once_per_rule() {
    with_test_ay_ctx_for_source(DYN_TO_DYN_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_to_dyn");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);

        let vc = ctx.chc_vc.as_ref().expect("CHC VC should be populated after CHC codegen");

        let env = constant_env(vc);
        let mut saw_a_vtable_binding = false;
        for rule in &vc.rules {
            for (out_var, values) in vtable_out_bindings(rule.body.constraints.iter()) {
                saw_a_vtable_binding = true;
                let mut consts: Vec<String> =
                    values.iter().filter_map(|v| resolve_const(v, &env)).collect();
                consts.sort();
                consts.dedup();
                assert!(
                    consts.len() <= 1,
                    "rule with head `{}` binds {out_var} to {} DIFFERENT constants \
                     ({consts:?}); disagreeing bindings make the block UNSAT, which \
                     silently turns the harness vacuous instead of failing",
                    rule.head.name,
                    consts.len(),
                );
            }
        }

        assert!(
            saw_a_vtable_binding,
            "probe should exercise vtable tracking — if this fires the test no \
             longer covers the dyn->dyn path and must be repaired, not deleted"
        );
    });

}
