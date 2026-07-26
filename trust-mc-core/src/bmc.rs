// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bounded Model Checking (BMC) verification conditions.
//!
//! BMC VCs represent bounded/acyclic verification problems where:
//! - SAT means a counterexample exists (property violation found)
//! - UNSAT means the property holds within the bound
//!
//! ## Query Strategy
//!
//! The BMC query uses an OR-of-violations approach:
//! ```text
//! SAT(path_constraints ∧ (violation₁ ∨ violation₂ ∨ ...))
//! ```
//!
//! If satisfiable, the model reveals which violation is triggered
//! and the concrete inputs that cause it.

use crate::decl::Decl;
use crate::violation::Violation;
use ay_bindings::Expr;

/// A Bounded Model Checking verification condition.
///
/// This represents a bounded verification problem for a single harness.
/// The emitter converts this to an SMT query where SAT indicates a
/// counterexample exists.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BmcVc {
    /// Declarations for symbolic constants, functions, and datatypes.
    pub decls: Vec<Decl>,

    /// Path constraints that must hold for any valid execution.
    ///
    /// These are AND'd together: all constraints must be satisfied.
    pub constraints: Vec<Expr>,

    /// Potential property violations to check.
    ///
    /// These are OR'd in the query: if any violation is satisfiable,
    /// the property fails.
    pub violations: Vec<Violation>,

    /// The query configuration.
    pub query: BmcQuery,

    /// Expressions to query for model values (used for concrete playback).
    ///
    /// These are emitted as `(get-value ...)` commands after check-sat
    /// when model production is enabled. Typically includes kani::any_raw
    /// symbolic variables and violation predicates.
    pub model_queries: Vec<Expr>,
}

impl BmcVc {
    /// Creates a new empty BMC VC.
    pub fn new() -> Self {
        Self {
            decls: Vec::new(),
            constraints: Vec::new(),
            violations: Vec::new(),
            query: BmcQuery::default(),
            model_queries: Vec::new(),
        }
    }

    /// Adds a declaration.
    pub fn add_decl(&mut self, decl: Decl) {
        self.decls.push(decl);
    }

    /// Adds a path constraint.
    pub fn add_constraint(&mut self, constraint: Expr) {
        self.constraints.push(constraint);
    }

    /// Adds a potential violation.
    pub fn add_violation(&mut self, violation: Violation) {
        self.violations.push(violation);
    }

    /// Adds an expression to query for model values.
    ///
    /// These expressions will be queried via `(get-value ...)` after check-sat
    /// when model production is enabled. Used for concrete playback and
    /// identifying which specific property was violated.
    pub fn add_model_query(&mut self, expr: Expr) {
        self.model_queries.push(expr);
    }

    /// Adds multiple expressions to query for model values.
    pub fn add_model_queries(&mut self, exprs: impl IntoIterator<Item = Expr>) {
        self.model_queries.extend(exprs);
    }

    /// Returns `true` if there are no violations to check.
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        self.violations.is_empty()
    }

    /// Returns the number of properties being checked.
    #[must_use]
    pub fn property_count(&self) -> usize {
        self.violations.len()
    }
}

impl Default for BmcVc {
    fn default() -> Self {
        Self::new()
    }
}

/// Query configuration for BMC verification.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct BmcQuery {
    /// Whether to request a model on SAT.
    pub produce_model: bool,

    /// Whether to request unsat cores on UNSAT.
    pub produce_unsat_core: bool,

    /// Optional timeout in milliseconds.
    pub timeout_ms: Option<u64>,

    /// The SMT logic to use (e.g., "QF_BV", "QF_AUFBV").
    pub logic: Option<String>,
}

impl BmcQuery {
    /// Creates a new query configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enables model production on SAT.
    #[must_use]
    pub fn with_model(mut self) -> Self {
        self.produce_model = true;
        self
    }

    /// Enables unsat core production on UNSAT.
    #[must_use]
    pub fn with_unsat_core(mut self) -> Self {
        self.produce_unsat_core = true;
        self
    }

    /// Sets the timeout.
    #[must_use]
    pub fn with_timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = Some(ms);
        self
    }

    /// Sets the SMT logic.
    #[must_use]
    pub fn with_logic(mut self, logic: impl Into<String>) -> Self {
        self.logic = Some(logic.into());
        self
    }
}
