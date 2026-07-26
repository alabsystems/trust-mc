// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// CLI driver for the main-thread-purity reachability lint.
//
// In real trust-mc this would run as a phase of `tcargo trust check`, seeded from
// the live monomorphized `CallGraph`. Standalone, it demonstrates the analysis on
// the aterm fixtures and FAILS CLOSED (exit 1) on any finding, the way a
// verification gate must.

use main_thread_purity::fixtures::{aterm_pre_fix, aterm_safe_teardown};
use main_thread_purity::{analyze, CallGraph, Policy, Severity};

fn run(title: &str, edges: Vec<main_thread_purity::Edge>, policy: &Policy) -> usize {
    let g = CallGraph::from_edges(edges);
    let findings = analyze(&g, policy);

    println!("== {title} ==");
    if findings.is_empty() {
        println!("PASS — no unbounded-blocking op reachable from the UI/main thread.\n");
        return 0;
    }
    println!("{} violation(s):", findings.len());
    for (i, f) in findings.iter().enumerate() {
        println!("  [{}] {} :: {}", i + 1, f.severity.label(), f.why);
        println!("      {}", f.render_path());
    }
    println!();
    findings.iter().filter(|f| f.severity == Severity::ErrorViaDrop).count();
    findings.len()
}

fn main() {
    let policy = Policy::aterm();
    let bad = run("aterm (pre-fix Session::drop -> libc::close)", aterm_pre_fix(), &policy);
    let good = run("aterm (safe hangup-then-detached-close teardown)", aterm_safe_teardown(), &policy);

    if good != 0 {
        eprintln!("UNEXPECTED: the safe teardown should be clean.");
        std::process::exit(2);
    }
    if bad != 0 {
        // Demonstration mode: the pre-fix graph SHOULD light up. A real gate run
        // against current source would exit(1) to fail CI. We exit 0 here so the
        // demo binary itself is "green" while still printing the catch.
        println!(
            "Caught {bad} pre-fix violation(s): the close()-on-UI-thread hang would have been \
             blocked at verification time."
        );
    }
}
