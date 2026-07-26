// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Diagnostic test: compile a DT solver harness and dump gap reasons.
//! Part of #4099: identifies the specific inline walker bail-out patterns
//! that generate 69+ sound_fallbacks in the tier3_dt harnesses.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::codegen_function::codegen_function_with_body;
use crate::codegen_ay::emit_chc;

const DT_UNION_TRANSITIVITY_SOURCE: &str = r#"
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

    pub fn probe_dt_union_transitivity() {
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

#[test]
fn test_dt_union_transitivity_gap_diagnostic() {
    use crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
    use crate::codegen_ay::chc::codegen_ctx::globals::{
        take_translation_drop_by_fn, take_translation_drop_site_reasons_by_fn,
    };

    // Drain all global counters before encoding
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let _ = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();
    let _ = take_translation_drop_by_fn();
    let _ = take_translation_drop_site_reasons_by_fn();

    let mut smt_len = 0usize;
    with_test_ay_ctx_for_source(DT_UNION_TRANSITIVITY_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.function_inlining = true;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, "probe_dt_union_transitivity");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);
        if let Some(chc_vc) = ctx.chc_vc.as_ref() {
            smt_len = emit_chc(chc_vc).to_string().len();
        }
    });

    // Capture sound fallback (translation_drop) reasons
    let td_by_fn = take_translation_drop_by_fn();
    let td_reasons = take_translation_drop_site_reasons_by_fn();

    // Capture aggregate encoding gap reasons
    let agg_gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let agg_gaps = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let agg_reasons = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();

    eprintln!("\n=== DT Union Transitivity Gap Diagnostic ===");
    eprintln!("SMT length: {smt_len} chars");
    eprintln!("\n--- Sound Fallback (translation_drop) by fn ---");
    for (fn_name, count) in &td_by_fn {
        eprintln!("  {count:3} x {fn_name}");
    }
    eprintln!("\n--- Sound Fallback Reasons ---");
    let mut all_td: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for (_fn_name, reasons) in &td_reasons {
        for (reason, count) in reasons {
            *all_td.entry(reason.clone()).or_default() += count;
        }
    }
    let mut sorted: Vec<_> = all_td.iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(a.1));
    for (reason, count) in &sorted {
        eprintln!("  {count:3} x {reason}");
    }

    eprintln!("\n--- Aggregate Encoding Gap ---");
    eprintln!("Total: {agg_gap_count}");
    for (fn_name, count) in &agg_gaps {
        eprintln!("  {count:3} x {fn_name}");
    }
    let mut all_agg: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for (_fn_name, reasons) in &agg_reasons {
        for (reason, count) in reasons {
            *all_agg.entry(reason.clone()).or_default() += count;
        }
    }
    if !all_agg.is_empty() {
        let mut sorted: Vec<_> = all_agg.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, count) in &sorted {
            eprintln!("  {count:3} x {reason}");
        }
    }
    eprintln!("=== End Diagnostic ===\n");
}
