// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-property CHC error relations (BSEM-18).
//!
//! Historically every check in a harness (bounds, overflow, alignment,
//! div-by-zero, user assert, UB check, contract check, memory-init) derived a
//! single nullary `error()` relation. A run could therefore report at most one
//! undifferentiated failure per harness — no way to name the property, attach
//! its message/kind, report multiple independent failures, or mark an
//! individually-unreachable check as such.
//!
//! This module introduces **per-property error relations**. Each distinct
//! check site derives its own `error_p{id}` relation, which is *bridged* into
//! the aggregate `error` relation with a rule `error_p{id} → error`.
//!
//! Keeping `error` as the sole query target is deliberate: the entire
//! solve/verdict machinery (trivially-safe short-circuit, straight-line
//! discharge, the portfolio `(query error)`) is unchanged, so soundness of the
//! aggregate verdict is byte-for-byte preserved. `error` is reachable iff some
//! `error_p{id}` is reachable, so no failure can be lost. The per-property
//! relations add naming: a counterexample trace passes through the specific
//! `error_p{id}` it violated, and on a proof each `error_p{id}` is individually
//! unreachable, so the driver can report per-property verdicts.
//!
//! Property ids are a per-harness sequence number allocated in deterministic
//! MIR traversal order (no RNG, no hashmap iteration order, no timestamps), so
//! results are reproducible and diffable across runs.

use trust_mc_core::chc::{ChcProperty, RelationApp, RelationDecl, Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

use super::ChcCtx;

/// Upper bound on distinct per-property relations emitted per harness.
///
/// Beyond this many check sites, further checks fall back to heading the
/// aggregate `error` relation directly (no distinct relation, no property
/// record). This is sound — such a check still makes `error` reachable, so the
/// harness still fails if the check is violated — it only forgoes the *named*
/// per-property breakdown for pathologically check-dense harnesses, bounding
/// the extra relation/rule count the solver must process.
pub(in crate::codegen_ay::chc) const MAX_CHC_PROPERTIES: usize = 256;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Allocate a per-property error relation head for a check site (BSEM-18).
    ///
    /// Returns the [`RelationApp`] the caller should use as the *head* of its
    /// error rule (`from ∧ ¬cond → <head>`). The returned head is a fresh
    /// nullary `error_p{id}` relation, which this function declares and bridges
    /// into `error` (`error_p{id} → error`); it also records the [`ChcProperty`]
    /// so the metadata reaches the VC artifact.
    ///
    /// Once [`MAX_CHC_PROPERTIES`] distinct properties have been registered,
    /// this returns the aggregate `error` head instead (see the constant docs).
    pub(in crate::codegen_ay::chc) fn register_error_head(
        &mut self,
        kind: PropertyKind,
        bb_idx: usize,
        message: Option<String>,
    ) -> RelationApp {
        if self.vc.properties.len() >= MAX_CHC_PROPERTIES {
            // Graceful degradation: fall back to the aggregate error head.
            return RelationApp::new("error", Vec::new());
        }

        let id = self.vc.properties.len() as u32;
        let relation = format!("error_p{id}");

        // Declare the nullary per-property relation.
        self.vc.add_relation(RelationDecl::nullary(relation.clone()));

        // Bridge into the aggregate `error` query relation: `error_p{id} → error`.
        // This keeps `error` reachable iff this property's check is reachable.
        self.vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::nullary(relation.as_str())), Vec::new()),
            RelationApp::nullary("error"),
        ));

        // Record the deterministic property metadata for the VC artifact.
        self.vc.add_property(ChcProperty {
            id,
            kind,
            bb: bb_idx,
            relation: relation.clone(),
            message,
            location: None,
            // Task #78: filled in at VC finalization by the dependence analysis.
            approximation_dependent: None,
        });

        RelationApp::new(relation, Vec::new())
    }
}
