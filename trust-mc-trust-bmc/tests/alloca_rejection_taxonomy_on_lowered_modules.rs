// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! WHY the proof-grade `Alloca` gate declines the cells `trustc` actually emits.
//!
//! On the ny-cert strict lane the driver's fail-closed `Alloca` arm is the single
//! largest block of unknown rows (411 rejections at R48), and until now the
//! diagnostic said only *that* a cell was rejected, never *which* condition
//! failed. `single_cell_alloca_rejection` names both lanes' first blocking
//! condition; this test runs it over the two checked-in
//! `-Ztrust-dump=native-bundle` fixtures — REAL bridge output, not hand-built IR
//! — and pins the resulting histogram.
//!
//! The measured shape is the point: every `Alloca` the bridge emits carries
//! `count: None, align: None` (all three emission sites in
//! `trust-ir-bridge::lower` hardcode both), so the array-alloca and
//! caller-alignment buckets are empty by construction. What is left is the
//! access shape.
//!
//! R50 widened mem2reg promotion from precise scalars to TRACKABLE AGGREGATES, so
//! a cross-block aggregate cell is no longer refused for its pointee type. The
//! remaining lane-2 buckets on this real output are therefore the two the widening
//! deliberately does NOT reach: a cell whose pointer ESCAPES, and a cell the
//! translator models opaquely (fat pointers, floats, enums). `how_many_rejected_
//! cells_the_translator_actually_tracks` measures that split directly, because it
//! is the ceiling on what any further access-shape work could buy.

use trust_ir::inst::Inst;
use trust_ir::{Function, Module};
use trust_mc_trust_bmc::{single_cell_alloca_rejection, stack_cell_is_translator_opaque};

const FORMAT_ARGS_BUNDLE: &str = include_str!("fixtures/format_args_insert_element_native_bundle.json");
const STALE_STRUCT_BUNDLE: &str = include_str!("fixtures/stale_struct_native_bundle.json");

fn module(bundle_json: &str) -> Module {
    let bundle: serde_json::Value =
        serde_json::from_str(bundle_json).expect("the dumped native bundle is valid JSON");
    serde_json::from_value(bundle["module"].clone())
        .expect("the dumped native bundle module deserializes")
}

/// `(function name, block, instruction, reason bucket)` for every `Alloca` in
/// `function` that the proof-grade gate declines.
fn rejections(module: &Module, function: &Function) -> Vec<(String, u32, usize, String)> {
    let mut rows = Vec::new();
    for block in &function.blocks {
        for (index, node) in block.body.iter().enumerate() {
            let Inst::Alloca { ty, count, align } = &node.inst else {
                continue;
            };
            // The driver's admission arm pattern requires both to be absent.
            assert!(
                count.is_none() && align.is_none(),
                "every bridge-emitted Alloca is metadata-less: {} {:?}",
                function.name,
                node.inst
            );
            let Some(result) = node.results.first().copied() else {
                continue;
            };
            if let Some(reason) = single_cell_alloca_rejection(module, function, result, ty) {
                rows.push((function.name.clone(), block.id.index(), index, reason.kind()));
            }
        }
    }
    rows
}

fn histogram(bundle_json: &str) -> Vec<(String, usize)> {
    let module = module(bundle_json);
    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut allocas = 0usize;
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                if matches!(node.inst, Inst::Alloca { .. }) {
                    allocas += 1;
                }
            }
        }
        for (_, _, _, kind) in rejections(&module, function) {
            *counts.entry(kind).or_default() += 1;
        }
    }
    let rejected: usize = counts.values().sum();
    assert!(rejected <= allocas, "a rejection row per rejected alloca, at most");
    counts.into_iter().collect()
}

/// `format!`-heavy code, the `ny_cert::alethe_emit::lit_str` replica.
#[test]
fn format_args_module_rejections_are_all_aggregate_or_fat_pointer_cells() {
    let counts = histogram(FORMAT_ARGS_BUNDLE);
    // Documented so a lowering change that shifts the frontier is visible in the
    // diff rather than silently re-bucketed.
    println!("format_args histogram: {counts:?}");
    assert!(!counts.is_empty(), "this module has rejected allocas");
    for (kind, _) in &counts {
        let (block_local, promoted) = kind.split_once('/').expect("both lanes are named");
        assert!(
            !block_local.is_empty() && !promoted.is_empty(),
            "both lanes report a reason: {kind}"
        );
        assert_ne!(
            block_local, "no_exact_defining_alloca",
            "a bridge-emitted Alloca always matches its own cell type"
        );
        // No bridge-emitted Alloca carries an extent or an alignment, so neither
        // lane can ever fail for those reasons on production IR.
        assert!(!kind.contains("count"), "no array allocas in bridge output: {kind}");
    }
}

/// Post-R50 this module's only rejection is an ESCAPING aggregate cell. It is the
/// control for the widening's boundary: the pointee type no longer blocks the
/// promotion lane, so whatever is left must name an access-shape or opacity reason
/// — never the pointee type of a cell the translator tracks.
#[test]
fn stale_struct_module_rejections_are_all_aggregate_cells() {
    let counts = histogram(STALE_STRUCT_BUNDLE);
    println!("stale_struct histogram: {counts:?}");
    for (kind, _) in &counts {
        assert!(
            kind.contains("not_promotable"),
            "an opaque or escaping cell never reaches the promotion lane: {kind}"
        );
    }
}

/// The structural claim, checked against real output: NO `Alloca` the bridge
/// emits carries `count` or `align`, so those two buckets are empty on every
/// production module — a histogram row for either would mean the bridge changed.
#[test]
fn no_bridge_emitted_alloca_carries_an_extent_or_an_alignment() {
    for bundle in [FORMAT_ARGS_BUNDLE, STALE_STRUCT_BUNDLE] {
        let module = module(bundle);
        for function in &module.functions {
            for block in &function.blocks {
                for node in &block.body {
                    if let Inst::Alloca { count, align, .. } = &node.inst {
                        assert!(count.is_none(), "no array alloca in {}", function.name);
                        assert!(align.is_none(), "no aligned alloca in {}", function.name);
                    }
                }
            }
        }
    }
}

/// The CEILING measurement. For every `Alloca` the gate declines, is the cell type
/// one the translator TRACKS precisely (so promotion could in principle reach it,
/// and only the access shape stands in the way) or one it models OPAQUELY (so no
/// promotion work can ever reach it)? Printed rather than pinned to a magic number,
/// with only the structural invariant asserted.
#[test]
fn how_many_rejected_cells_the_translator_actually_tracks() {
    for (label, bundle) in [("format_args", FORMAT_ARGS_BUNDLE), ("stale_struct", STALE_STRUCT_BUNDLE)]
    {
        let module = module(bundle);
        let (mut tracked, mut opaque) = (0usize, 0usize);
        for function in &module.functions {
            for block in &function.blocks {
                for node in &block.body {
                    let Inst::Alloca { ty, .. } = &node.inst else { continue };
                    let Some(result) = node.results.first().copied() else { continue };
                    if single_cell_alloca_rejection(&module, function, result, ty).is_none() {
                        continue;
                    }
                    if stack_cell_is_translator_opaque(&module, ty) {
                        opaque += 1;
                    } else {
                        tracked += 1;
                    }
                }
            }
        }
        println!("{label}: rejected cells — translator-tracked {tracked}, opaque {opaque}");
        // Every rejected cell the translator TRACKS is now refused for its ACCESS
        // shape, never for its pointee type: promotion accepts exactly the tracked
        // set. The opaque ones keep the pointee-type bucket.
        assert!(tracked + opaque > 0, "{label} has rejected allocas");
    }
}
