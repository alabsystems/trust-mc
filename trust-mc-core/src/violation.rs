// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Violation and property types for structured failure reporting.
//!
//! Violations represent potential property failures that the solver checks.
//! They preserve structured labels so the driver can map failures to
//! meaningful Kani property kinds.

use crate::ident::{PropertyId, SourceLocation};
use ay_bindings::Expr;
use serde::{Deserialize, Serialize};

/// A potential property violation.
///
/// This represents a condition that, if satisfiable, indicates a property
/// failure. The driver uses the structured metadata to produce meaningful
/// diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Violation {
    /// Unique identifier for this property.
    pub property_id: PropertyId,
    /// The kind of property being checked.
    pub kind: PropertyKind,
    /// The condition that, if true, indicates a violation.
    ///
    /// In BMC mode, this is OR'd into the query: `SAT(violation1 | violation2 | ...)`
    /// means at least one property can fail.
    pub condition: Expr,
    /// Source location of the check.
    pub location: Option<SourceLocation>,
    /// Additional context for the violation message.
    pub message: Option<String>,
    /// SMT variable name for this violation (#1164).
    ///
    /// Stores the exact SMT variable name (e.g., "ay_violation_pointer_invalid_0")
    /// for consistent mapping in the VC artifact. This is needed because the
    /// original label may differ from `kind.label()`.
    pub smt_var: Option<String>,
    /// SMT variable name of the per-check reachability flag (BMC).
    ///
    /// The flag is defined as the check's guard (path condition conjoined with
    /// the ordered assumption context at the check site). The driver classifies
    /// the check as UNREACHABLE when the solver proves the flag unsatisfiable.
    /// `None` means the guard is trivially `true` (always reachable).
    pub reach_var: Option<String>,
}

impl Violation {
    /// Creates a new violation.
    pub fn new(property_id: PropertyId, kind: PropertyKind, condition: Expr) -> Self {
        Self {
            property_id,
            kind,
            condition,
            location: None,
            message: None,
            smt_var: None,
            reach_var: None,
        }
    }

    /// Sets the source location.
    #[must_use]
    pub fn with_location(mut self, location: SourceLocation) -> Self {
        self.location = Some(location);
        self
    }

    /// Sets the violation message.
    #[must_use]
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }

    /// Sets the SMT variable name (#1164).
    #[must_use]
    pub fn with_smt_var(mut self, smt_var: impl Into<String>) -> Self {
        self.smt_var = Some(smt_var.into());
        self
    }

    /// Sets the reachability flag variable name.
    #[must_use]
    pub fn with_reach_var(mut self, reach_var: impl Into<String>) -> Self {
        self.reach_var = Some(reach_var.into());
        self
    }
}

/// The kind of property being checked.
///
/// This corresponds to Kani's property classification system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PropertyKind {
    /// User-written assertion: `kani::assert(cond, msg)`
    Assertion,
    /// Assumption: `kani::assume(cond)`
    Assumption,
    /// Cover statement: `kani::cover(cond, msg)`
    Cover,
    /// Arithmetic overflow check.
    ArithmeticOverflow,
    /// Division by zero check.
    DivisionByZero,
    /// Array bounds check.
    OutOfBounds,
    /// Null pointer dereference check.
    NullPointer,
    /// Memory safety check (e.g., use after free).
    MemorySafety,
    /// Pointer offset overflow check.
    PointerOverflow,
    /// Unreachable code check.
    Unreachable,
    /// Panic handler reached.
    Panic,
    /// Undefined behavior check.
    UndefinedBehavior,
    /// Contract precondition.
    Precondition,
    /// Contract postcondition.
    Postcondition,
    /// Loop invariant.
    LoopInvariant,
    /// Loop variant / `decreases` ranking check (termination measure).
    LoopDecreases,
    /// Other/unclassified check.
    Other,
}

impl PropertyKind {
    /// Returns a human-readable description of this property kind.
    pub fn description(&self) -> &'static str {
        match self {
            PropertyKind::Assertion => "assertion",
            PropertyKind::Assumption => "assumption",
            PropertyKind::Cover => "cover",
            PropertyKind::ArithmeticOverflow => "arithmetic overflow",
            PropertyKind::DivisionByZero => "division by zero",
            PropertyKind::OutOfBounds => "out of bounds access",
            PropertyKind::NullPointer => "null pointer dereference",
            PropertyKind::MemorySafety => "memory safety",
            PropertyKind::PointerOverflow => "pointer overflow",
            PropertyKind::Unreachable => "unreachable code",
            PropertyKind::Panic => "panic",
            PropertyKind::UndefinedBehavior => "undefined behavior",
            PropertyKind::Precondition => "precondition",
            PropertyKind::Postcondition => "postcondition",
            PropertyKind::LoopInvariant => "loop invariant",
            PropertyKind::LoopDecreases => "loop decreases ranking",
            PropertyKind::Other => "check",
        }
    }

    /// Returns the label string used in violation predicate naming.
    ///
    /// This matches the labels used by the legacy codegen path and parsed
    /// by the driver's ay_parse module. The format is `ay_violation_<label>_<N>`.
    pub fn label(&self) -> &'static str {
        match self {
            PropertyKind::Assertion => "kani_assert",
            PropertyKind::Assumption => "kani_assume",
            PropertyKind::Cover => "kani_cover",
            PropertyKind::ArithmeticOverflow => "overflow_check",
            PropertyKind::DivisionByZero => "div_by_zero_check",
            PropertyKind::OutOfBounds => "bounds_check",
            PropertyKind::NullPointer => "null_pointer_check",
            PropertyKind::MemorySafety => "memory_safety_check",
            PropertyKind::PointerOverflow => "pointer_overflow_check",
            PropertyKind::Unreachable => "unreachable",
            PropertyKind::Panic => "panic",
            PropertyKind::UndefinedBehavior => "undefined_behavior",
            PropertyKind::Precondition => "precondition",
            PropertyKind::Postcondition => "postcondition",
            PropertyKind::LoopInvariant => "loop_invariant",
            PropertyKind::LoopDecreases => "loop_decreases_check",
            PropertyKind::Other => "assertion",
        }
    }
}

impl std::fmt::Display for PropertyKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}
