// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Extended diagnostic: encode the FULL 11-field DtSolver through CHC pipeline
//! and dump the VC structure. Part of #4099.
//!
//! Previous diagnostic (test_dt_solver_gap_diagnostic.rs) used a 3-field struct
//! and showed 0 SFB. This test uses the exact source from the real test file
//! to reproduce the 82-relation system that produces CTREX.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::codegen_function::codegen_function_with_body;
use crate::codegen_ay::emit_chc;

/// Exact source from tests/ay/ay_self_verify_bootstrap_tier3_dt.rs
/// with only the union_transitivity harness.
const DT_FULL_UNION_TRANSITIVITY: &str = r#"
    #![allow(dead_code)]

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct DtSolver {
        parent0: u32,
        parent1: u32,
        parent2: u32,
        ctor0: u32,
        ctor1: u32,
        ctor2: u32,
        scope_len: usize,
        scope0_ctor_count: usize,
        scope1_ctor_count: usize,
        ctor_count: usize,
        has_datatype: bool,
    }

    impl DtSolver {
        fn new() -> Self {
            Self {
                parent0: 0, parent1: 1, parent2: 2,
                ctor0: 0, ctor1: 0, ctor2: 0,
                scope_len: 0, scope0_ctor_count: 0, scope1_ctor_count: 0,
                ctor_count: 0, has_datatype: false,
            }
        }

        fn find(&self, x: u32) -> u32 {
            let p0 = self.get_parent(x);
            if p0 == x { return x; }
            let p1 = self.get_parent(p0);
            if p1 == p0 { return p0; }
            p1
        }

        fn get_parent(&self, x: u32) -> u32 {
            match x {
                0 => self.parent0,
                1 => self.parent1,
                2 => self.parent2,
                _ => x,
            }
        }

        fn set_parent(&mut self, x: u32, p: u32) {
            match x {
                0 => self.parent0 = p,
                1 => self.parent1 = p,
                2 => self.parent2 = p,
                _ => {}
            }
        }

        fn union(&mut self, x: u32, y: u32) {
            let rx = self.find(x);
            let ry = self.find(y);
            if rx != ry {
                self.set_parent(rx, ry);
            }
        }
    }

    pub fn probe_dt_union_transitivity_full() {
        let mut solver = DtSolver::new();
        solver.union(0, 1);
        solver.union(1, 2);
        let r0 = solver.find(0);
        let r1 = solver.find(1);
        let r2 = solver.find(2);
        assert_eq!(r0, r1);
        assert_eq!(r1, r2);
        assert_eq!(r0, r2);
    }
"#;

/// Minimized 3-field version (only parent fields, no ctor/scope).
/// If this ALSO produces CTREX in the same pipeline, the 11 fields aren't
/// the problem — the match-arm mutation pattern is.
const DT_MINIMAL_UNION_TRANSITIVITY: &str = r#"
    #![allow(dead_code)]

    struct UF3 {
        parent0: u32,
        parent1: u32,
        parent2: u32,
    }

    impl UF3 {
        fn new() -> Self {
            Self { parent0: 0, parent1: 1, parent2: 2 }
        }

        fn find(&self, x: u32) -> u32 {
            let p0 = self.get_parent(x);
            if p0 == x { return x; }
            let p1 = self.get_parent(p0);
            if p1 == p0 { return p0; }
            p1
        }

        fn get_parent(&self, x: u32) -> u32 {
            match x {
                0 => self.parent0,
                1 => self.parent1,
                2 => self.parent2,
                _ => x,
            }
        }

        fn set_parent(&mut self, x: u32, p: u32) {
            match x {
                0 => self.parent0 = p,
                1 => self.parent1 = p,
                2 => self.parent2 = p,
                _ => {}
            }
        }

        fn union(&mut self, x: u32, y: u32) {
            let rx = self.find(x);
            let ry = self.find(y);
            if rx != ry {
                self.set_parent(rx, ry);
            }
        }
    }

    pub fn probe_uf3_union_transitivity() {
        let mut solver = UF3::new();
        solver.union(0, 1);
        solver.union(1, 2);
        let r0 = solver.find(0);
        let r1 = solver.find(1);
        let r2 = solver.find(2);
        assert!(r0 == r1);
        assert!(r1 == r2);
    }
"#;

/// Encode a source through the full pipeline, return (smt_len, relation_count, rule_count, smt_text).
fn encode_and_measure(source: &str, fn_suffix: &str) -> (usize, usize, usize, String) {
    let mut smt_text = String::new();
    let mut rel_count = 0usize;
    let mut rule_count = 0usize;

    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.function_inlining = true;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);
        if let Some(chc_vc) = ctx.chc_vc.as_ref() {
            smt_text = emit_chc(chc_vc).to_string();
            rel_count = chc_vc.relations.len();
            rule_count = chc_vc.rules.len();
        }
    });

    eprintln!("\n=== Encoding Measurement: {fn_suffix} ===");
    eprintln!("SMT length: {} chars", smt_text.len());
    eprintln!("Relations: {rel_count}");
    eprintln!("Rules: {rule_count}");

    // Dump first 200 lines of SMT for inspection
    let lines: Vec<&str> = smt_text.lines().collect();
    eprintln!("\n--- SMT2 (first 200 lines) ---");
    for (i, line) in lines.iter().take(200).enumerate() {
        eprintln!("{:4}: {}", i + 1, line);
    }
    if lines.len() > 200 {
        eprintln!("... ({} more lines)", lines.len() - 200);
    }

    // Look for error relation and assertions
    eprintln!("\n--- Error/Assert rules ---");
    for (i, line) in lines.iter().enumerate() {
        if line.contains("error") || line.contains("assert") || line.contains("chc_err") {
            eprintln!("{:4}: {}", i + 1, line);
        }
    }
    eprintln!("=== End ===\n");

    (smt_text.len(), rel_count, rule_count, smt_text)
}

#[test]
fn test_full_dt_union_transitivity_encoding() {
    let (smt_len, rels, rules, smt_text) =
        encode_and_measure(DT_FULL_UNION_TRANSITIVITY, "probe_dt_union_transitivity_full");

    eprintln!("Full 11-field DtSolver: smt_len={smt_len}, rels={rels}, rules={rules}");
    assert!(smt_len > 0, "SMT output must be non-empty");
    assert!(rels > 0, "Must produce at least one relation");

    // Write SMT2 to /tmp for manual Z3 testing
    let path = "/tmp/dt_full_union_transitivity.smt2";
    std::fs::write(path, &smt_text).expect("write smt2");
    eprintln!("SMT2 written to {path}");
}

#[test]
fn test_minimal_uf3_union_transitivity_encoding() {
    let (smt_len, rels, rules, smt_text) =
        encode_and_measure(DT_MINIMAL_UNION_TRANSITIVITY, "probe_uf3_union_transitivity");

    eprintln!("Minimal 3-field UF3: smt_len={smt_len}, rels={rels}, rules={rules}");
    assert!(smt_len > 0, "SMT output must be non-empty");
    assert!(rels > 0, "Must produce at least one relation");

    // Write SMT2 to /tmp for manual Z3 testing
    let path = "/tmp/uf3_union_transitivity.smt2";
    std::fs::write(path, &smt_text).expect("write smt2");
    eprintln!("SMT2 written to {path}");
}
