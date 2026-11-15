// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for alloc_view.rs: naming the allocation a pointer term points into,
//! and Kani's same-allocation predicate over two named allocations.

use ay_bindings::{Expr, ExprValue};

use super::*;
use crate::codegen_ay::context::AllocView;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort, ptr_sort};

fn view(root: &str, offset: u128, extent: u128) -> AllocView {
    AllocView { root: std::sync::Arc::from(root), offset, extent }
}

/// A pointer derived from a registered address symbol — through an SSA
/// definition, a `+` of an offset, or an `ite` whose other arm is an
/// `__ssa_init_` placeholder — names that symbol's allocation. Arms from two
/// allocations, a sum of two addresses, and an undefined variable name none.
/// Two different root locals are two allocations (the predicate is `false`);
/// one root gives the in-bounds conjunction, never a constant.
#[test]
fn test_resolve_alloc_and_same_allocation() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn alloc_probe(x: u32) -> u32 {
            x
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "alloc_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let s = codegen.ctx.declare_var("probe::a_addr", ptr_sort());
            codegen.ctx.alloc_views.insert("probe::a_addr".to_string(), view("probe::a", 4, 16));
            let t = codegen.ctx.declare_var("probe::b_addr", ptr_sort());
            codegen.ctx.alloc_views.insert("probe::b_addr".to_string(), view("probe::b", 0, 8));

            let p = codegen.ctx.declare_var("probe::p_0", ptr_sort());
            codegen.ssa_concrete_values.insert(
                "probe::p_0".to_string(),
                s.clone().bvadd(Expr::bitvec_const(8u128, POINTER_WIDTH)),
            );
            let (sym, v) = codegen.resolve_alloc(&p).expect("p is derived from a");
            assert!(sym == s);
            assert_eq!(v, view("probe::a", 4, 16));

            let c = codegen.ctx.declare_var("probe::c_0", bool_sort());
            let init = codegen.ctx.declare_var("probe::q__ssa_init_1", ptr_sort());
            let q = Expr::ite(c.clone(), s.clone(), init);
            assert!(codegen.resolve_alloc(&q).is_some_and(|(sym, _)| sym == s));

            let mixed = Expr::ite(c, s.clone(), t.clone());
            assert!(codegen.resolve_alloc(&mixed).is_none(), "two allocations name none");
            assert!(codegen.resolve_alloc(&s.clone().bvadd(t.clone())).is_none());

            let u = codegen.ctx.declare_var("probe::u_0", ptr_sort());
            assert!(codegen.resolve_alloc(&u).is_none(), "an undefined pointer names none");

            let different = codegen.same_allocation_exact(&s, &s, &t, &t).expect("both named");
            assert!(matches!(different.value(), ExprValue::BoolConst(false)));
            let same = codegen.same_allocation_exact(&p, &p, &s, &s).expect("both named");
            assert!(!matches!(same.value(), ExprValue::BoolConst(_)));
        },
    );
}

/// The `probe_<N>_addr` symbols a fragment of SMT text names, in order of
/// appearance.
fn probe_symbols(text: &str) -> Vec<usize> {
    let mut found = Vec::new();
    let mut rest = text;
    while let Some(at) = rest.find("probe_") {
        rest = &rest[at + "probe_".len()..];
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        if !digits.is_empty() && rest[digits.len()..].starts_with("_addr") {
            found.push(digits.parse().expect("digits"));
        }
    }
    found
}

/// Two live locals are two allocations: `register_alloc_view` asserts each new
/// root apart from every root registered before it. Those assertions follow the
/// registration order, so the SMT text is the same on every run. The roots used
/// to live in a std `HashMap`, which emitted them in a per-process random order:
/// two runs of one bundle handed `ay` the same assertions in two orders, and a
/// BMC verdict sensitive to that order flipped between FAILED and INCONCLUSIVE
/// (`loop_contract_register_walk_dual.rs::inv_oob_bug`, measured 2026-10-01).
#[test]
fn test_alloc_root_disjointness_follows_registration_order() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn roots_probe(a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32) -> u32 {
            a ^ b ^ c ^ d ^ e ^ f ^ g ^ h
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "roots_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // The eight arguments, registered in an order that matches neither
            // their local index nor their name order.
            let order = [5usize, 2, 8, 1, 7, 3, 6, 4];
            for (i, &local) in order.iter().enumerate() {
                let addr = codegen
                    .ctx
                    .declare_var(&format!("roots_probe::probe_{local}_addr"), ptr_sort());
                let before = codegen.ctx.program.to_string().len();
                codegen.register_alloc_view(&addr, &Place { local, projection: vec![] });
                let emitted = codegen.ctx.program.to_string()[before..].to_string();
                // Every assertion that names this root and another one is a
                // disjointness assertion; read the other root off each.
                let earlier: Vec<usize> = emitted
                    .lines()
                    .filter_map(|line| {
                        let named = probe_symbols(line);
                        let other: Vec<usize> =
                            named.iter().copied().filter(|n| *n != local).collect();
                        if other.is_empty() {
                            return None;
                        }
                        assert!(named.contains(&local), "{line}");
                        assert!(other.iter().all(|n| *n == other[0]), "{line}");
                        Some(other[0])
                    })
                    .collect();
                assert_eq!(earlier, order[..i], "root {local}: disjointness in registration order");
            }
            let bases: Vec<usize> = codegen
                .ctx
                .alloc_roots
                .values()
                .map(|(base, _)| probe_symbols(&base.to_string())[0])
                .collect();
            assert_eq!(bases, order, "the roots keep their registration order");
        },
    );
}
