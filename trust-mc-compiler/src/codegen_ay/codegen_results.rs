// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY codegen result aggregation — `AYCodegenResults` struct and metadata generation.

use crate::args::ReachabilityType;
use crate::codegen_ay::context::MinimalAYCtx;
use crate::kani_middle::analysis;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::MonoItem;
use std::collections::BTreeMap;
use std::fmt::Write;
use trust_mc_metadata::{HarnessMetadata, KaniMetadata, UnsupportedFeature};

use super::unsoundness_fields::collect_unsoundness_fields;

/// Results from AY code generation.
pub(super) struct AYCodegenResults {
    reachability: ReachabilityType,
    harnesses: Vec<HarnessMetadata>,
    unsupported_constructs: BTreeMap<String, Vec<String>>,
    items: Vec<MonoItem>,
    crate_name: String,
}

impl AYCodegenResults {
    fn build_metadata(
        reachability: ReachabilityType,
        harnesses: Vec<HarnessMetadata>,
        unsupported_constructs: BTreeMap<String, Vec<String>>,
        crate_name: String,
    ) -> KaniMetadata {
        let unsupported_features = unsupported_constructs
            .into_iter()
            .map(|(feature, locations)| UnsupportedFeature {
                feature,
                locations: locations
                    .into_iter()
                    .map(|filename| trust_mc_metadata::Location { filename, start_line: 0 })
                    .collect(),
            })
            .collect();

        let (proofs, tests) = if reachability == ReachabilityType::Harnesses {
            (harnesses, vec![])
        } else {
            (vec![], harnesses)
        };

        let uf = collect_unsoundness_fields();

        KaniMetadata {
            crate_name,
            proof_harnesses: proofs,
            unsupported_features,
            test_harnesses: tests,
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: uf.iterator_unsoundness,
            bigint_unsoundness: uf.bigint_unsoundness,
            chc_fallbacks: uf.chc_fallbacks,
            chc_translation_drops: uf.chc_translation_drops,
            chc_coerce_eq_drops: uf.chc_coerce_eq_drops,
            assume_dropped_transitions: uf.assume_dropped_transitions,
            store_dropped_transitions: uf.store_dropped_transitions,
            constant_zero_fallbacks: uf.constant_zero_fallbacks,
            unhandled_calls: uf.unhandled_calls,
            error_blocked_fmt: uf.error_blocked_fmt,
            known_stdlib_unconstrained: uf.known_stdlib_unconstrained,
            inferable_predicates: uf.inferable_predicates,
            diverging_call_drops: uf.diverging_call_drops,
            offset_provenance_unresolved: uf.offset_provenance_unresolved,
            assert_untranslatable: uf.assert_untranslatable,
            heap_check_untranslatable: uf.heap_check_untranslatable,
            heap_check_unknown_layout: uf.heap_check_unknown_layout,
            type_sort_fallbacks: uf.type_sort_fallbacks,
            signedness_fallbacks: uf.signedness_fallbacks,
            into_option_drops: uf.into_option_drops,
            internal_workarounds: uf.internal_workarounds,
            abstracted_fallbacks: uf.abstracted_fallbacks,
            vec_field_fallbacks: uf.vec_field_fallbacks,
            pointee_synthesis_fallbacks: uf.pointee_synthesis_fallbacks,
            unsupported_construct_fallbacks: uf.unsupported_construct_fallbacks,
            bmc_store_coercion_fallbacks: uf.bmc_store_coercion_fallbacks,
            kani_mem_overapprox: uf.kani_mem_overapprox,
            sort_harmonize_fresh_var_fallbacks: uf.sort_harmonize_fresh_var_fallbacks,
            unconstrained_assignments: uf.unconstrained_assignments,
            ptr_metadata_unconstrained: uf.ptr_metadata_unconstrained,
            static_init_incomplete: uf.static_init_incomplete,
            fp_bitvector_encoding: uf.fp_bitvector_encoding,
            aggregate_encoding_gap: uf.aggregate_encoding_gap,
            stub_approximation: uf.stub_approximation,
            rounding_assertion_bypass: uf.rounding_assertion_bypass,
        }
    }

    /// Creates a new empty codegen results container.
    ///
    /// REQUIRES: `tcx` is the type context for the current crate.
    /// ENSURES: Returned container has empty harnesses and items.
    /// ENSURES: Returned container records the crate name from `tcx`.
    pub(super) fn new(tcx: TyCtxt, reachability: ReachabilityType) -> Self {
        AYCodegenResults {
            reachability,
            harnesses: vec![],
            unsupported_constructs: BTreeMap::new(),
            items: vec![],
            crate_name: tcx.crate_name(LOCAL_CRATE).as_str().to_owned(),
        }
    }

    /// Generates Kani metadata from codegen results.
    ///
    /// REQUIRES: Codegen has completed (harnesses and constructs populated).
    /// ENSURES: Returned metadata includes all proof and test harnesses.
    /// ENSURES: Returned metadata includes unsupported features.
    /// ENSURES: Returned metadata includes iterator unsoundness info if counters > 0.
    #[cfg(test)]
    pub(super) fn generate_metadata(&self) -> KaniMetadata {
        Self::build_metadata(
            self.reachability,
            self.harnesses.clone(),
            self.unsupported_constructs.clone(),
            self.crate_name.clone(),
        )
    }

    pub(super) fn into_metadata(self) -> KaniMetadata {
        Self::build_metadata(
            self.reachability,
            self.harnesses,
            self.unsupported_constructs,
            self.crate_name,
        )
    }

    pub(super) fn extend(
        &mut self,
        min_ctx: MinimalAYCtx,
        items: Vec<MonoItem>,
        metadata: Option<HarnessMetadata>,
    ) {
        let mut items = items;
        self.harnesses.extend(metadata);
        for (k, v) in min_ctx.unsupported_constructs {
            // Convert &'static str key to String for BTreeMap serialization boundary.
            self.unsupported_constructs.entry(k.into()).or_default().extend(v);
        }
        self.items.append(&mut items);
    }

    pub(super) fn print_report(&self, tcx: TyCtxt) {
        if !self.unsupported_constructs.is_empty() {
            let mut msg = String::from("AY backend: Found the following unsupported constructs:\n");
            for (construct, locations) in &self.unsupported_constructs {
                let _ = writeln!(&mut msg, "    - {} ({}):", construct, locations.len());
                for loc in locations.iter().take(5) {
                    let _ = writeln!(&mut msg, "      * {}", loc);
                }
                if locations.len() > 5 {
                    let _ = writeln!(&mut msg, "      ... and {} more", locations.len() - 5);
                }
            }
            msg.push_str(
                "\nVerification will fail if one or more of these constructs is reachable.",
            );
            tcx.dcx().warn(msg);
        }

        if tracing::enabled!(tracing::Level::INFO) {
            analysis::print_stats(&self.items);
        }
    }

    /// Format the unsupported constructs report string (without emitting diagnostics).
    ///
    /// Extracted for testability -- `print_report` requires `TyCtxt` but the
    /// formatting logic is pure string manipulation.
    #[cfg(test)]
    fn format_unsupported_report(&self) -> Option<String> {
        if self.unsupported_constructs.is_empty() {
            return None;
        }
        let mut msg = String::from("AY backend: Found the following unsupported constructs:\n");
        for (construct, locations) in &self.unsupported_constructs {
            // fmt::Write for String is infallible.
            let _ = writeln!(&mut msg, "    - {} ({}):", construct, locations.len());
            for loc in locations.iter().take(5) {
                let _ = writeln!(&mut msg, "      * {}", loc);
            }
            if locations.len() > 5 {
                let _ = writeln!(&mut msg, "      ... and {} more", locations.len() - 5);
            }
        }
        msg.push_str("\nVerification will fail if one or more of these constructs is reachable.");
        Some(msg)
    }
}

#[cfg(test)]
mod tests;
