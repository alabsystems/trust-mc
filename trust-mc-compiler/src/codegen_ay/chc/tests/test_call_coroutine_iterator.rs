// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed localizer for iterator-count coroutine wrapper shapes.
//!
//! Part of #4150: three-tier gate to identify where `constraint_invariant_fixup`
//! and `inline_drop_walk_failed` first appear in the W<T>/chain/eq pipeline.
//!
//! Tier 1: wrapper-only `next()` — W<T> with a single resume
//! Tier 2: wrapper + `chain(...)` — two W<T> iterators chained
//! Tier 3: wrapper + `chain(...)` + `eq(...)` — full consumer pipeline

#![allow(clippy::panic, clippy::unwrap_used)]

use super::common::*;
use rustc_public::mir::{Rvalue, StatementKind};

/// Tier 1: Wrapper-only next() probe.
///
/// Minimal W<T> iterator with a single coroutine that yields one value.
/// Tests whether the wrapper/resume dispatch alone introduces fixups.
const WRAPPER_ONLY_NEXT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    pub fn probe_wrapper_only_next() -> bool {
        let g = #[coroutine] || {
            yield 1u8;
            yield 2u8;
        };
        let mut w = W(g);
        let first = w.next();
        first == Some(1u8)
    }
"#;

/// Tier 2: Wrapper + chain probe.
///
/// Two W<T> iterators chained together. Tests whether chain() introduces
/// fixups beyond what the wrapper alone produces.
const WRAPPER_CHAIN_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    pub fn probe_wrapper_chain() -> bool {
        let g1 = #[coroutine] || { yield 1u8; };
        let g2 = #[coroutine] || { yield 2u8; };
        let mut chained = W(g1).chain(W(g2));
        let first = chained.next();
        first == Some(1u8)
    }
"#;

/// Tier 3: Wrapper + chain + eq consumer probe.
///
/// Matches the production iterator-count.rs shape: W<T>.chain(W<T>).eq(range).
/// Tests whether the equality consumer introduces additional fixups.
const WRAPPER_CHAIN_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    pub fn probe_wrapper_chain_eq() -> bool {
        let g1 = #[coroutine] || { yield 1u8; yield 2u8; };
        let g2 = #[coroutine] || { yield 3u8; };
        W(g1).chain(W(g2)).eq(1u8..4u8)
    }
"#;

/// Tier 1b: Wrapper with for-loop range yield.
///
/// The production iterator-count.rs uses `for i in start..end { yield i }`
/// inside the coroutine, which generates range iterator + loop MIR. This is
/// structurally different from literal yields.
const WRAPPER_RANGE_YIELD_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    pub fn probe_wrapper_range_yield() -> bool {
        let g = #[coroutine] || {
            for i in 1u8..4u8 {
                yield i;
            }
        };
        let mut w = W(g);
        w.next() == Some(1u8)
    }
"#;

/// Tier 2b: Closure-returning-coroutine probe.
///
/// The production harness uses `|start| { #[coroutine] move || { for i in start..end { yield i } } }`
/// — a closure that captures `end` and returns a `move` coroutine. This creates
/// nested-capture MIR that the literal-yield and direct-coroutine probes lack.
const CLOSURE_RETURNING_COROUTINE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    pub fn probe_closure_returning_coroutine() -> bool {
        let end = 6u8;
        let closure_test = |start: u8| {
            #[coroutine]
            move || {
                for i in start..end {
                    yield i;
                }
            }
        };
        let mut w = W(closure_test(1));
        w.next() == Some(1u8)
    }
"#;

/// Tier 3c: Full production-matching shape with closure-returning-coroutine.
///
/// Exact replica of iterator-count.rs architecture:
/// - named function returning a coroutine
/// - closure capturing `end` returning a `move` coroutine
/// - chain + eq consumer
const FULL_PRODUCTION_SHAPE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    fn test() -> impl Coroutine<(), Return = (), Yield = u8> + Unpin {
        #[coroutine]
        || {
            for i in 1u8..6u8 {
                yield i;
            }
        }
    }

    pub fn probe_full_production_shape() -> bool {
        let end = 11u8;
        let closure_test = |start: u8| {
            #[coroutine]
            move || {
                for i in start..end {
                    yield i;
                }
            }
        };
        W(test()).chain(W(closure_test(6))).eq(1u8..11u8)
    }
"#;

/// Tier 3b: Production-matching shape with for-loop coroutines + chain + eq.
///
/// Closest reduced form to the actual iterator-count.rs harness:
/// - W<T> wrapper with for-loop range coroutines
/// - chain() combining two W<T> iterators
/// - eq() consumer comparing against a range
const WRAPPER_RANGE_CHAIN_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::marker::Unpin;
    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    struct W<T>(T);

    impl<T: Coroutine<(), Return = ()> + Unpin> Iterator for W<T> {
        type Item = T::Yield;

        fn next(&mut self) -> Option<Self::Item> {
            match Pin::new(&mut self.0).resume(()) {
                CoroutineState::Complete(..) => None,
                CoroutineState::Yielded(v) => Some(v),
            }
        }
    }

    fn test_coro() -> impl Coroutine<(), Return = (), Yield = u8> + Unpin {
        #[coroutine] || {
            for i in 1u8..4u8 {
                yield i;
            }
        }
    }

    pub fn probe_wrapper_range_chain_eq() -> bool {
        let g2 = #[coroutine] || {
            for i in 4u8..6u8 {
                yield i;
            }
        };
        W(test_coro()).chain(W(g2)).eq(1u8..6u8)
    }
"#;

/// Exact committed harness file used by the authoritative compiletest run.
const ITERATOR_COUNT_REAL_FILE: &str = include_str!(
    "../../../../../tests/trust_mc/Coroutines/rustc-coroutine-tests/iterator-count.rs"
);

/// Strip Kani-only attributes/comments so the committed harness source compiles
/// under the unit-test translation harness.
fn strip_kani_attrs_for_unit_ctx(source: &str) -> String {
    let mut result = String::with_capacity(source.len());
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.starts_with("// compile-flags:")
            || trimmed.starts_with("// kani-flags:")
            || trimmed.starts_with("//!")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

/// Match the compiletest CHC lane for the real `iterator-count.rs` harness.
fn iterator_compiletest_config() -> ChcConfig {
    ChcConfig {
        track_level: ChcTrackLevel::Mem,
        step_mode: crate::args::ChcStepMode::Auto,
        // `iterator-count.rs` runs as a proof harness with `#[kani::unwind(11)]`.
        // Mirror that recursive inline budget here so unit localizers inspect the
        // same call-graph regime as compiletest.
        recursive_unwind_depth: 11,
        unwinding_assertions: true,
        ..ChcConfig::default()
    }
}

type TranslationSiteReasons =
    std::collections::BTreeMap<String, std::collections::BTreeMap<String, usize>>;
type RangeSpecNextPathCounts =
    super::super::call::codegen_call_iterator_adapter::RangeSpecNextPathCounts;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IteratorMalformedBvBoundary {
    RangeIteratorComposition,
    FlatteningOrProjection,
    LaterSolverRewrite,
}

fn looks_like_flattening_or_projection(label: &str) -> bool {
    let label = label.to_ascii_lowercase();
    label.contains("flatten") || label.contains("project")
}

fn classify_iterator_malformed_bv_boundary(
    first_malformed_bv: Option<&MalformedBvSite>,
    range_spec_next_paths: &RangeSpecNextPathCounts,
    translation_sites: Option<&TranslationSiteReasons>,
) -> IteratorMalformedBvBoundary {
    let Some(site) = first_malformed_bv else {
        return IteratorMalformedBvBoundary::LaterSolverRewrite;
    };

    let flattening_signal = looks_like_flattening_or_projection(&site.head_relation)
        || translation_sites.is_some_and(|sites| {
            sites.iter().any(|(fn_name, reasons)| {
                looks_like_flattening_or_projection(fn_name)
                    || reasons.keys().any(|reason| looks_like_flattening_or_projection(reason))
            })
        });
    if flattening_signal {
        return IteratorMalformedBvBoundary::FlatteningOrProjection;
    }

    if range_spec_next_paths.datatype + range_spec_next_paths.flattened > 0 {
        return IteratorMalformedBvBoundary::RangeIteratorComposition;
    }

    IteratorMalformedBvBoundary::RangeIteratorComposition
}

/// Diagnostic counters extracted from a full translation pass.
#[derive(Debug)]
struct IteratorDiagnostics {
    constraint_invariant_fixup: usize,
    inline_drop_walk_failed: usize,
    sound_fallback_count: usize,
    call_dispatch_fallback: usize,
    relation_count: usize,
    rule_count: usize,
    range_spec_next_paths: RangeSpecNextPathCounts,
    first_malformed_bv: Option<MalformedBvSite>,
    malformed_bv_boundary: IteratorMalformedBvBoundary,
}

impl IteratorDiagnostics {
    fn from_translation(source: &str, fn_name: &str) -> Self {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let before_range_spec_next_paths =
            super::super::call::codegen_call_iterator_adapter::get_range_spec_next_path_counts();
        let mut result = None;
        with_test_ay_ctx_for_source(source, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, iterator_compiletest_config());
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

            let constraint_invariant_fixup = diagnostics
                .sound_fallback_detail
                .get("constraint_invariant_fixup")
                .copied()
                .unwrap_or(0);
            let inline_drop_walk_failed = diagnostics
                .sound_fallback_detail
                .get("inline_drop_walk_failed")
                .copied()
                .unwrap_or(0);
            let sound_fallback_count: usize = diagnostics.sound_fallback_detail.values().sum();
            let call_dispatch_fallback = diagnostics
                .sound_fallback_detail
                .get("call_dispatch_fallback")
                .copied()
                .unwrap_or(0);
            let first_malformed_bv = first_malformed_bv_site(&vc);
            let after_range_spec_next_paths =
                super::super::call::codegen_call_iterator_adapter::get_range_spec_next_path_counts(
                );
            let range_spec_next_paths = RangeSpecNextPathCounts {
                datatype: after_range_spec_next_paths.datatype
                    - before_range_spec_next_paths.datatype,
                flattened: after_range_spec_next_paths.flattened
                    - before_range_spec_next_paths.flattened,
                fail_closed: after_range_spec_next_paths.fail_closed
                    - before_range_spec_next_paths.fail_closed,
            };

            result = Some(IteratorDiagnostics {
                constraint_invariant_fixup,
                inline_drop_walk_failed,
                sound_fallback_count,
                call_dispatch_fallback,
                relation_count: vc.relations.len(),
                rule_count: vc.rules.len(),
                malformed_bv_boundary: classify_iterator_malformed_bv_boundary(
                    first_malformed_bv.as_ref(),
                    &range_spec_next_paths,
                    None,
                ),
                range_spec_next_paths,
                first_malformed_bv,
            });
        });
        result.expect("translation should complete")
    }
}

#[derive(Debug)]
struct IteratorExactFileFallbackSnapshot {
    rule_count: usize,
    sound_fallback_detail: std::collections::BTreeMap<String, usize>,
    translation_sites: TranslationSiteReasons,
    range_spec_next_paths: RangeSpecNextPathCounts,
    first_malformed_bv: Option<MalformedBvSite>,
    malformed_bv_boundary: IteratorMalformedBvBoundary,
}

impl IteratorExactFileFallbackSnapshot {
    fn sound_fallback_count(&self, reason: &str) -> usize {
        self.sound_fallback_detail.get(reason).copied().unwrap_or(0)
    }

    fn total_reason_count(&self, reason: &str) -> usize {
        self.translation_sites
            .values()
            .map(|reasons| reasons.get(reason).copied().unwrap_or(0))
            .sum()
    }

    fn owners_for_reason(&self, reason: &str) -> Vec<String> {
        self.translation_sites
            .iter()
            .filter_map(|(fn_name, reasons)| {
                reasons.get(reason).copied().filter(|count| *count > 0).map(|_| fn_name.clone())
            })
            .collect()
    }
}

fn reset_iterator_localizer_metadata() {
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
}

/// Run a compiletest-equivalent localizer on the committed iterator-count
/// source. Unlike the reduced probes, this mirrors the proof-harness path more
/// closely by:
/// - translating the real committed harness body
/// - matching CHC Mem-track + Auto step mode
/// - bounded-unrolling `main` with the harness' `#[kani::unwind(11)]`
fn run_real_iterator_count_fallback_localizer() -> IteratorExactFileFallbackSnapshot {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_iterator_localizer_metadata();

    let mut rule_count = 0usize;
    let mut sound_fallback_detail = std::collections::BTreeMap::new();
    let mut first_malformed_bv = None;
    let before_range_spec_next_paths =
        super::super::call::codegen_call_iterator_adapter::get_range_spec_next_path_counts();
    let source = format!(
        "#![allow(dead_code)]\n{}",
        strip_kani_attrs_for_unit_ctx(ITERATOR_COUNT_REAL_FILE)
    );
    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "main");
        let body = instance.body().expect("main body");
        let cfg = iterator_compiletest_config();
        let unrolled = crate::codegen_ay::loop_unroll::unroll_cfg_loops(
            body.clone(),
            cfg.recursive_unwind_depth,
            cfg.unwinding_assertions,
        )
        .expect("iterator-count main should bounded-unroll under #[kani::unwind(11)]");
        let chc_ctx = ChcCtx::new(ctx.tcx, &unrolled, "main", cfg);
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        rule_count = vc.rules.len();
        sound_fallback_detail = diagnostics
            .sound_fallback_detail
            .into_iter()
            .map(|(reason, count)| (reason.to_string(), count))
            .collect();
        first_malformed_bv = first_malformed_bv_site(&vc);
    });
    let after_range_spec_next_paths =
        super::super::call::codegen_call_iterator_adapter::get_range_spec_next_path_counts();
    let range_spec_next_paths = RangeSpecNextPathCounts {
        datatype: after_range_spec_next_paths.datatype - before_range_spec_next_paths.datatype,
        flattened: after_range_spec_next_paths.flattened - before_range_spec_next_paths.flattened,
        fail_closed: after_range_spec_next_paths.fail_closed
            - before_range_spec_next_paths.fail_closed,
    };
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let malformed_bv_boundary = classify_iterator_malformed_bv_boundary(
        first_malformed_bv.as_ref(),
        &range_spec_next_paths,
        Some(&translation_sites),
    );

    IteratorExactFileFallbackSnapshot {
        rule_count,
        sound_fallback_detail,
        translation_sites,
        range_spec_next_paths,
        first_malformed_bv,
        malformed_bv_boundary,
    }
}

/// Tier 1: wrapper-only next() — identify baseline fixup count.
#[test]
fn test_tier1_wrapper_only_next_diagnostics() {
    run_with_large_stack(|| {
        let diag = IteratorDiagnostics::from_translation(
            WRAPPER_ONLY_NEXT_SOURCE,
            "probe_wrapper_only_next",
        );

        // Record the baseline. The key question: does the wrapper shape alone
        // produce constraint_invariant_fixup?
        eprintln!(
            "TIER1 wrapper-only: constraint_invariant_fixup={}, inline_drop_walk_failed={}, \
             total_fallback={}, relations={}, rules={}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        // Structural: the translation must produce a valid VC
        assert!(
            diag.relation_count >= 2,
            "tier1: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier1: expected >= 1 rule, got {}", diag.rule_count);
    });
}

/// Tier 2: wrapper + chain — identify if chain() adds fixups.
#[test]
fn test_tier2_wrapper_chain_diagnostics() {
    run_with_large_stack(|| {
        let diag =
            IteratorDiagnostics::from_translation(WRAPPER_CHAIN_SOURCE, "probe_wrapper_chain");

        eprintln!(
            "TIER2 wrapper+chain: constraint_invariant_fixup={}, inline_drop_walk_failed={}, \
             total_fallback={}, relations={}, rules={}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        assert!(
            diag.relation_count >= 2,
            "tier2: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier2: expected >= 1 rule, got {}", diag.rule_count);
    });
}

/// Tier 3: wrapper + chain + eq — full consumer pipeline matching iterator-count.rs.
#[test]
fn test_tier3_wrapper_chain_eq_diagnostics() {
    run_with_large_stack(|| {
        let diag = IteratorDiagnostics::from_translation(
            WRAPPER_CHAIN_EQ_SOURCE,
            "probe_wrapper_chain_eq",
        );

        eprintln!(
            "TIER3 wrapper+chain+eq: constraint_invariant_fixup={}, inline_drop_walk_failed={}, \
             total_fallback={}, relations={}, rules={}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        assert!(
            diag.relation_count >= 2,
            "tier3: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier3: expected >= 1 rule, got {}", diag.rule_count);
    });
}

/// Tier 1b: wrapper with for-loop range yield — isolates the range-iterator
/// MIR complexity that the production harness has but literal-yield probes lack.
#[test]
fn test_tier1b_wrapper_range_yield_diagnostics() {
    run_with_large_stack(|| {
        let diag = IteratorDiagnostics::from_translation(
            WRAPPER_RANGE_YIELD_SOURCE,
            "probe_wrapper_range_yield",
        );

        eprintln!(
            "TIER1b wrapper+range-yield: constraint_invariant_fixup={}, inline_drop_walk_failed={}, \
             total_fallback={}, relations={}, rules={}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        assert!(
            diag.relation_count >= 2,
            "tier1b: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier1b: expected >= 1 rule, got {}", diag.rule_count);
    });
}

/// Tier 3b: production-matching shape — for-loop coroutines + chain + eq.
/// This is the closest reduced form to the actual iterator-count.rs harness.
#[test]
fn test_tier3b_wrapper_range_chain_eq_diagnostics() {
    run_with_large_stack(|| {
        let diag = IteratorDiagnostics::from_translation(
            WRAPPER_RANGE_CHAIN_EQ_SOURCE,
            "probe_wrapper_range_chain_eq",
        );

        eprintln!(
            "TIER3b wrapper+range+chain+eq: constraint_invariant_fixup={}, inline_drop_walk_failed={}, \
             total_fallback={}, relations={}, rules={}, range_spec_next_paths={:?}, \
             first_malformed_bv={:?}, malformed_bv_boundary={:?}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
            diag.range_spec_next_paths,
            diag.first_malformed_bv,
            diag.malformed_bv_boundary,
        );

        assert!(
            diag.relation_count >= 2,
            "tier3b: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier3b: expected >= 1 rule, got {}", diag.rule_count);

        // #4184: The emitted VC must be free of malformed BV nodes.
        // The BV-width panic at ay-core extract_concat occurs at a later
        // solver-facing rewrite boundary, not in trust_mc's codegen layer.
        assert!(
            diag.first_malformed_bv.is_none(),
            "tier3b: emitted VC should contain no malformed BvConcat/BvExtract nodes; \
             got {:?}",
            diag.first_malformed_bv,
        );
        assert_eq!(
            diag.malformed_bv_boundary,
            IteratorMalformedBvBoundary::LaterSolverRewrite,
            "tier3b: boundary should classify as LaterSolverRewrite when VC is clean",
        );
    });
}

/// Tier 2b: closure-returning-coroutine — isolates the nested-capture pattern.
#[test]
fn test_tier2b_closure_returning_coroutine_diagnostics() {
    run_with_large_stack(|| {
        let diag = IteratorDiagnostics::from_translation(
            CLOSURE_RETURNING_COROUTINE_SOURCE,
            "probe_closure_returning_coroutine",
        );

        eprintln!(
            "TIER2b closure-returning-coroutine: constraint_invariant_fixup={}, \
             inline_drop_walk_failed={}, total_fallback={}, relations={}, rules={}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        assert!(
            diag.relation_count >= 2,
            "tier2b: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier2b: expected >= 1 rule, got {}", diag.rule_count);
    });
}

/// Tier 3c: full production shape — named fn + closure-coroutine + chain + eq.
/// This is the exact architectural replica of iterator-count.rs.
#[test]
fn test_tier3c_full_production_shape_diagnostics() {
    run_with_large_stack(|| {
        let diag = IteratorDiagnostics::from_translation(
            FULL_PRODUCTION_SHAPE_SOURCE,
            "probe_full_production_shape",
        );

        eprintln!(
            "TIER3c full-production: constraint_invariant_fixup={}, inline_drop_walk_failed={}, \
             total_fallback={}, relations={}, rules={}",
            diag.constraint_invariant_fixup,
            diag.inline_drop_walk_failed,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        assert!(
            diag.relation_count >= 2,
            "tier3c: expected >= 2 relations, got {}",
            diag.relation_count
        );
        assert!(diag.rule_count >= 1, "tier3c: expected >= 1 rule, got {}", diag.rule_count);
    });
}

/// Part of #4160: verify the reduced Chain probe stays off call_dispatch_fallback.
///
/// Before the fix, Chain fell through translate_adt_ty() to bv32, causing the
/// inline walker to emit call_dispatch_fallback. With Chain encoded as ptr_sort(),
/// the reduced wrapper probe stays clean. The real harness' Chain aggregate is
/// localized separately below.
#[test]
fn test_chain_encoding_eliminates_call_dispatch_fallback() {
    run_with_large_stack(|| {
        let diag =
            IteratorDiagnostics::from_translation(WRAPPER_CHAIN_SOURCE, "probe_wrapper_chain");

        eprintln!(
            "chain_encoding: call_dispatch_fallback={}, sound_fallback_count={}, \
             relations={}, rules={}",
            diag.call_dispatch_fallback,
            diag.sound_fallback_count,
            diag.relation_count,
            diag.rule_count,
        );

        assert_eq!(
            diag.call_dispatch_fallback, 0,
            "Chain encoding should eliminate call_dispatch_fallback, got {}",
            diag.call_dispatch_fallback
        );
    });
}

/// Part of #4160: the real `iterator-count.rs` harness reaches `std::iter::Chain`
/// construction through the resolved `Iterator::chain` callee body, and that
/// aggregate must honor the opaque pointer-width type encoding instead of
/// descending into nested iterator fields.
#[test]
fn test_real_iterator_count_chain_aggregate_translates_to_opaque_ptr() {
    run_with_large_stack(|| {
        let source = strip_kani_attrs_for_unit_ctx(ITERATOR_COUNT_REAL_FILE);
        with_test_ay_ctx_for_source(&source, |ctx| {
            let main_instance = find_instance_by_suffix(ctx.tcx, "main");
            let main_body = main_instance.body().expect("main body");
            let main_ctx = ChcCtx::new(ctx.tcx, &main_body, "main", iterator_compiletest_config());
            let chain_instance = main_ctx
                .resolve_body_call_instance_by_suffix(&main_body, "Iterator::chain")
                .expect("main should call Iterator::chain");
            let chain_body = chain_instance.body().expect("Iterator::chain body");
            let mut chain_ctx =
                ChcCtx::new(ctx.tcx, &chain_body, "Iterator::chain", iterator_compiletest_config());

            let chain_expr = chain_body
                .blocks
                .iter()
                .flat_map(|block| block.statements.iter())
                .find_map(|stmt| {
                    let StatementKind::Assign(
                        _,
                        Rvalue::Aggregate(
                            AggregateKind::Adt(def, variant_idx, args, _, _),
                            operands,
                        ),
                    ) = &stmt.kind
                    else {
                        return None;
                    };
                    if def.trimmed_name() != "Chain" {
                        return None;
                    }
                    chain_ctx.translate_adt_aggregate(
                        *def,
                        *variant_idx,
                        args,
                        operands,
                        &HashSet::new(),
                    )
                })
                .expect("Iterator::chain should construct a std::iter::Chain aggregate");

            assert_eq!(
                chain_expr.sort().bitvec_width(),
                Some(crate::codegen_ay::types::POINTER_WIDTH),
                "iterator-count Chain aggregate should translate as an opaque pointer-width value"
            );
        });
    });
}

/// Part of #4160: on current HEAD, the reduced probes and the exact-file
/// localizer both stay off `call_dispatch_fallback`. This test only proves the
/// old dispatch-fallback lane is consumed; any remaining authoritative
/// compiletest failure is now outside this localizer path.
#[test]
fn test_real_iterator_count_proof_harness_localizer_stays_off_call_dispatch_fallback() {
    run_with_large_stack(|| {
        let snapshot = run_real_iterator_count_fallback_localizer();
        let total_call_dispatch_fallbacks = snapshot.total_reason_count("call_dispatch_fallback");
        let sound_call_dispatch_fallbacks = snapshot.sound_fallback_count("call_dispatch_fallback");
        let call_dispatch_owners = snapshot.owners_for_reason("call_dispatch_fallback");

        eprintln!(
            "iterator_count_proof_harness_localizer: \
             total_call_dispatch_fallbacks={}, sound_call_dispatch_fallbacks={}, \
             owners={call_dispatch_owners:?}, rule_count={}, sound_fallback_detail={:?}, \
             translation_sites={:?}, range_spec_next_paths={:?}, first_malformed_bv={:?}, \
             malformed_bv_boundary={:?}",
            total_call_dispatch_fallbacks,
            sound_call_dispatch_fallbacks,
            snapshot.rule_count,
            snapshot.sound_fallback_detail,
            snapshot.translation_sites,
            snapshot.range_spec_next_paths,
            snapshot.first_malformed_bv,
            snapshot.malformed_bv_boundary,
        );

        assert_eq!(
            total_call_dispatch_fallbacks, 0,
            "proof-harness localizer should stay off call_dispatch_fallback on current HEAD; \
             sound_fallback_detail={:?}, owners={call_dispatch_owners:?}, \
             translation_sites={:?}",
            snapshot.sound_fallback_detail, snapshot.translation_sites,
        );
        assert_eq!(
            sound_call_dispatch_fallbacks, 0,
            "proof-harness localizer should keep sound_fallback_detail off \
             call_dispatch_fallback on current HEAD; sound_fallback_detail={:?}, \
             owners={call_dispatch_owners:?}, translation_sites={:?}",
            snapshot.sound_fallback_detail, snapshot.translation_sites,
        );
        assert!(
            call_dispatch_owners.is_empty(),
            "proof-harness localizer should not report fallback owners on current HEAD; \
             owners={call_dispatch_owners:?}, \
             sound_fallback_detail={:?}, translation_sites={:?}",
            snapshot.sound_fallback_detail,
            snapshot.translation_sites,
        );

        // #4184: The full harness VC must be free of malformed BV nodes.
        // The AY extract_concat panic is at a later solver-facing rewrite
        // boundary, not in trust_mc's emitted CHC rules.
        assert!(
            snapshot.first_malformed_bv.is_none(),
            "proof-harness localizer: emitted VC should contain no malformed \
             BvConcat/BvExtract nodes; got {:?}",
            snapshot.first_malformed_bv,
        );
        assert_eq!(
            snapshot.malformed_bv_boundary,
            IteratorMalformedBvBoundary::LaterSolverRewrite,
            "proof-harness localizer: boundary should classify as LaterSolverRewrite; \
             the BV-width panic is at the solver rewrite layer, not codegen",
        );
    });
}
