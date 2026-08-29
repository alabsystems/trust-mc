// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! VC artifact building and loop invariant hint extraction for AY codegen context.
//!
//! Extracted from context.rs as part of #2093.

use crate::kani_middle::transform::get_loop_invariants;
use trust_mc_core::artifact::{
    ArtifactMetadata, LoopInvariantHint, PropertyMetadata, VcArtifact, VerificationMode,
};
use trust_mc_core::ident::{HarnessId, PropertyId};

use super::AYCtx;

impl<'tcx, 't> AYCtx<'tcx, 't> {
    /// Build a VcArtifact from the current context's violations.
    ///
    /// Creates a serializable artifact containing property metadata for each
    /// violation. The driver uses this to map solver results back to source
    /// locations.
    ///
    /// # Arguments
    /// * `harness_name` - The name of the harness being verified
    /// * `smt_filename` - Optional path to the associated .smt2 file
    pub(in crate::codegen_ay) fn build_vc_artifact(
        &mut self,
        harness_name: &str,
        smt_filename: Option<&str>,
    ) -> VcArtifact {
        let harness = HarnessId::new(harness_name, harness_name);
        let mode = if self.config.use_chc { VerificationMode::Chc } else { VerificationMode::Bmc };

        let mut artifact = VcArtifact::new(harness).with_mode(mode);
        if let Some(smt_file) = smt_filename {
            artifact = artifact.with_smt_file(smt_file);
        }

        // Build PropertyMetadata for each violation in bmc_vc.
        // #1164: Use stored smt_var for exact variable name matching
        // Part of #2267: drain violations by value to avoid cloning 4 fields per violation
        // (property_id, smt_var, location, message). Safe because violations are not
        // accessed after build_vc_artifact in the production flow.
        for violation in std::mem::take(&mut self.bmc_vc.violations) {
            let var_name = violation.smt_var.unwrap_or_else(|| {
                use std::fmt::Write;
                let label = violation.kind.label();
                let mut s = String::with_capacity(14 + label.len() + 4);
                s.push_str("ay_violation_");
                s.push_str(label);
                s.push('_');
                let _ = write!(s, "{}", violation.property_id.id);
                s
            });
            #[allow(deprecated)] // Backward compatibility: populate both fields
            let mut prop = PropertyMetadata::new(violation.property_id, violation.kind)
                .with_violation_var(var_name.clone())
                .with_smt_var(var_name); // #1164: Also set smt_var for forward compatibility

            if let Some(loc) = violation.location {
                prop = prop.with_location(loc);
            }
            if let Some(msg) = violation.message {
                prop = prop.with_message(msg);
            }
            if let Some(reach_var) = violation.reach_var {
                prop = prop.with_reach_var(reach_var);
            }

            artifact.add_property(prop);
        }

        // BSEM-18: Add per-property CHC check metadata to the artifact.
        //
        // In CHC mode each check site emits an `error_p{id}` relation bridged
        // into the aggregate `error` query (see `chc::error_property`). We
        // surface one `PropertyMetadata` per registered check, keyed by the
        // relation name (`smt_var = "error_p{id}"`), so the driver can report
        // per-property verdicts. Pure metadata — the semantics live in the
        // emitted CHC rules, not here.
        if let Some(chc_vc) = self.chc_vc.as_ref() {
            for prop in &chc_vc.properties {
                let mut meta = PropertyMetadata::new(PropertyId::new(prop.id), prop.kind)
                    .with_smt_var(prop.relation.clone());
                if let Some(message) = &prop.message {
                    meta = meta.with_message(message.clone());
                }
                if let Some(location) = &prop.location {
                    meta = meta.with_location(location.clone());
                }
                // Task #78: per-property approximation-dependence verdict.
                if let Some(dependent) = prop.approximation_dependent {
                    meta = meta.with_approximation_dependent(dependent);
                }
                artifact.add_property(meta);
            }
            // Task #78: harness-level freed-var identities + completeness.
            artifact.approximated_vars = chc_vc.approximated_vars.clone();
            artifact.accounted_approximations = chc_vc.accounted_approximations;
            artifact.approximation_identity_complete = chc_vc.approximation_identity_complete;
        }

        // #1164: Add cover property metadata to artifact
        // Part of #2267: drain cover_metadata by value to avoid cloning 3-5 strings per cover.
        for cover in std::mem::take(&mut self.cover_metadata) {
            artifact.add_property(cover);
        }

        for coverage in std::mem::take(&mut self.coverage_metadata) {
            artifact.add_property(coverage);
        }

        // Positive evidence for the driver's vacuity decision: no obligation
        // SITE is reachable from this harness, so zero checks cannot be a
        // dropped obligation — it is the `fn check() {}` shape Kani reports as
        // a clean `0 of 0 failed`. See `obligation_free_walk`.
        //
        // Keyed by HARNESS. It was one shared flag, which made it meaningless
        // in a multi-harness file: codegen runs per function, artifacts are per
        // harness, so whichever function ran LAST answered for all of them.
        {
            if self.obligation_free_body_by_fn.get(harness_name).copied().unwrap_or(false) {
                let metadata = artifact.metadata.get_or_insert_with(ArtifactMetadata::default);
                metadata.obligation_free_body = Some(true);
            }
        }

        // Part of #972: Add loop invariant hints if CHC mode is enabled
        if self.config.use_chc {
            let loop_hints = self.build_loop_hints(harness_name);
            if !loop_hints.is_empty() {
                let metadata = artifact.metadata.get_or_insert_with(ArtifactMetadata::default);
                metadata.loop_hints = loop_hints;
            }
        }

        artifact
    }

    /// Build loop invariant hints from extracted MIR annotations.
    ///
    /// Part of #972: Converts `ExtractedLoopInvariant` from the global registry
    /// to serializable `LoopInvariantHint` structures for the VcArtifact.
    ///
    /// Part of #1562: Formula extraction from closure bodies.
    fn build_loop_hints(&mut self, harness_name: &str) -> Vec<LoopInvariantHint> {
        let Some(invariants) = get_loop_invariants(harness_name) else {
            return Vec::new();
        };

        invariants
            .iter()
            .map(|inv| {
                // CHC relation names follow the pattern "{fn_name}__bbN" (see ChcCtx::block_relation_name)
                // Part of #40: target the CHC-visible loop head (the register
                // call's terminator target) when recorded — the register-call
                // block itself has no matching relation, so hints named after
                // it were silently skipped by the driver.
                let hint_bb = inv.chc_loop_head_bb.unwrap_or(inv.loop_head_bb);
                let relation_name = {
                    use std::fmt::Write;
                    let mut s = String::with_capacity(harness_name.len() + 8);
                    s.push_str(harness_name);
                    s.push_str("__bb");
                    let _ = write!(s, "{}", hint_bb);
                    s
                };

                // Part of #3258: Prefer per-BB relation arg positions (captured_rel_arg_positions)
                // over the legacy chc_local_to_state_idx mapping. Per-BB positions correctly
                // account for dead-local elimination and tuple flattening.
                let captured_state_indices = inv.captured_rel_arg_positions.clone().or_else(|| {
                    self.chc_local_to_state_idx.get(harness_name).map(|mapping| {
                        inv.captured_vars
                            .iter()
                            .map(|local| mapping.get(local).copied().unwrap_or(*local))
                            .collect()
                    })
                });

                let mut hint = LoopInvariantHint::new(relation_name, inv.loop_head_bb)
                    .with_captured_vars(inv.captured_vars.clone());

                if let Some(state_indices) = captured_state_indices {
                    hint = hint.with_captured_state_indices(state_indices);
                }

                let formula = inv.formula_smt2.clone().or_else(|| {
                    crate::codegen_ay::loop_invariant::extract_loop_invariant_formula(
                        self.tcx,
                        harness_name,
                        inv,
                        self.config.chc_track_level,
                        self.config.chc_step_mode,
                        self.config.ay_wide_mem,
                    )
                });
                if let Some(formula) = formula {
                    hint = hint.with_formula_smt2(formula);
                }

                hint
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::super::with_test_ay_ctx;
    use ay_bindings::Expr;
    use trust_mc_core::artifact::VerificationMode;
    use trust_mc_core::ident::{PropertyId, SourceLocation};
    use trust_mc_core::violation::{PropertyKind, Violation};

    #[test]
    fn test_build_vc_artifact_bmc_mode_with_smt_file() {
        with_test_ay_ctx(|mut ctx| {
            let location = SourceLocation::new("src/lib.rs", 42)
                .with_column(7)
                .with_function("crate::harness");
            ctx.record_property_violation_with_location(
                Expr::bool_const(true),
                "kani_assert",
                Some(location.clone()),
            );

            let artifact = ctx.build_vc_artifact("crate::harness", Some("crate_harness.smt2"));

            assert_eq!(artifact.mode, VerificationMode::Bmc);
            assert_eq!(artifact.smt_file.as_deref(), Some("crate_harness.smt2"));
            assert_eq!(artifact.harness.mangled_name, "crate::harness");
            assert_eq!(artifact.harness.pretty_name, "crate::harness");
            assert_eq!(artifact.properties.len(), 1);
            assert_eq!(artifact.properties[0].kind, PropertyKind::Assertion);
            assert_eq!(artifact.properties[0].location.as_ref(), Some(&location));
            assert_eq!(
                artifact.properties[0].smt_var.as_deref(),
                Some("ay_violation_kani_assert_0")
            );
        });
    }

    #[test]
    fn test_build_vc_artifact_preserves_explicit_violation_smt_var() {
        with_test_ay_ctx(|mut ctx| {
            ctx.bmc_vc.add_violation(
                Violation::new(
                    PropertyId::new(7),
                    PropertyKind::NullPointer,
                    Expr::bool_const(true),
                )
                .with_smt_var("explicit_null_check"),
            );

            let artifact = ctx.build_vc_artifact("crate::harness", None);
            let matching: Vec<_> =
                artifact.properties.iter().filter(|prop| prop.id.id == 7).collect();
            assert_eq!(matching.len(), 1);
            assert_eq!(matching[0].smt_var.as_deref(), Some("explicit_null_check"));
            assert_eq!(matching[0].kind, PropertyKind::NullPointer);
        });
    }

    #[test]
    fn test_build_vc_artifact_generates_fallback_smt_var_when_missing() {
        with_test_ay_ctx(|mut ctx| {
            ctx.bmc_vc.add_violation(
                Violation::new(
                    PropertyId::new(9),
                    PropertyKind::DivisionByZero,
                    Expr::bool_const(true),
                )
                .with_message("div-by-zero path"),
            );

            let artifact = ctx.build_vc_artifact("crate::harness", None);
            let matching: Vec<_> =
                artifact.properties.iter().filter(|prop| prop.id.id == 9).collect();
            assert_eq!(matching.len(), 1);
            assert_eq!(matching[0].smt_var.as_deref(), Some("ay_violation_div_by_zero_check_9"));
            assert_eq!(matching[0].message.as_deref(), Some("div-by-zero path"));
        });
    }

    #[test]
    fn test_build_vc_artifact_appends_cover_metadata() {
        with_test_ay_ctx(|mut ctx| {
            let location = SourceLocation::new("src/cover.rs", 8).with_column(3);
            ctx.record_cover_property_with_location(
                Expr::bool_const(true),
                Some(location.clone()),
                Some("cover reached".to_string()),
            );

            let artifact = ctx.build_vc_artifact("crate::cover_harness", None);
            assert_eq!(artifact.properties.len(), 1);
            assert_eq!(artifact.properties[0].kind, PropertyKind::Cover);
            assert_eq!(artifact.properties[0].location.as_ref(), Some(&location));
            assert_eq!(artifact.properties[0].message.as_deref(), Some("cover reached"));
            assert!(
                artifact.properties[0]
                    .smt_var
                    .as_ref()
                    .is_some_and(|name| name.starts_with("ay_cover_"))
            );
        });
    }

    #[test]
    fn test_build_vc_artifact_chc_mode_without_registered_hints() {
        with_test_ay_ctx(|mut ctx| {
            ctx.config.use_chc = true;
            let hints = ctx.build_loop_hints("crate::missing_hints");
            assert!(hints.is_empty());

            let artifact = ctx.build_vc_artifact("crate::missing_hints", None);
            assert_eq!(artifact.mode, VerificationMode::Chc);
            assert!(artifact.metadata.is_none());
        });
    }
}
