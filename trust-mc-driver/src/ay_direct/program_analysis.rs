// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Program analysis for direct AY execution compatibility.
//!
//! Scans AYPrograms to detect features requiring SMT-LIB fallback.

use ay_bindings::AYProgram;
use ay_bindings::constraint::Constraint as BindingsConstraint;
use ay_bindings::expr::{Expr as BindingsExpr, ExprValue};
use ay_bindings::sort::SortInner as BindingsSortInner;

/// Features that require SMT-LIB fallback (not yet supported in direct path).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UnsupportedFeature {
    /// Algebraic datatypes (ay_dpll::api doesn't support datatypes yet)
    Datatype(String),
    /// CHC/Horn clause commands (DeclareRel, Rule, Query)
    ChcCommand,
    /// Quantifiers in expressions
    Quantifier,
    /// Soft assertions (optimization)
    SoftAssert,
    /// BV operations not in ay_dpll::api (div, rem, shifts, etc.)
    UnsupportedBvOp(&'static str),
    /// BV extend/extract operations
    UnsupportedBvExtend,
    /// Overflow detection operations
    UnsupportedOverflowCheck,
}

/// Result of analyzing a AYProgram for direct execution compatibility.
#[derive(Debug)]
pub(crate) struct ProgramAnalysis {
    /// Features that require fallback to SMT-LIB path
    pub unsupported: Vec<UnsupportedFeature>,
    /// Detected logic from SetLogic command (if any)
    pub detected_logic: Option<String>,
    /// Violation variable names found
    pub violations: Vec<String>,
}

impl ProgramAnalysis {
    /// Check if the program can be executed directly (no unsupported features).
    pub(crate) fn supports_direct_execution(&self) -> bool {
        self.unsupported.is_empty()
    }
}

/// Analyze a AYProgram to determine if it can be executed directly.
///
/// Scans for features that require SMT-LIB fallback:
/// - Datatype declarations or sorts
/// - CHC commands (DeclareRel, Rule, Query)
/// - Quantifiers in expressions
/// - Soft assertions
pub(crate) fn analyze_program(program: &AYProgram) -> ProgramAnalysis {
    let mut unsupported = Vec::new();
    let mut detected_logic = None;
    let mut violations = Vec::new();

    for constraint in program.commands() {
        match constraint {
            // Datatype declarations require fallback
            BindingsConstraint::DeclareDatatype(dt) => {
                unsupported.push(UnsupportedFeature::Datatype(dt.name.clone()));
            }

            // CHC commands require fallback
            BindingsConstraint::DeclareRel { .. }
            | BindingsConstraint::Rule { .. }
            | BindingsConstraint::Query(_) => {
                if !unsupported.contains(&UnsupportedFeature::ChcCommand) {
                    unsupported.push(UnsupportedFeature::ChcCommand);
                }
            }

            // Soft assertions require fallback
            BindingsConstraint::SoftAssert { .. } => {
                if !unsupported.contains(&UnsupportedFeature::SoftAssert) {
                    unsupported.push(UnsupportedFeature::SoftAssert);
                }
            }

            // Track logic and violations
            BindingsConstraint::SetLogic(logic) => {
                detected_logic = Some(logic.clone());
            }
            BindingsConstraint::DeclareConst { name, sort } => {
                // Check for datatype sorts
                if let BindingsSortInner::Datatype(dt) = sort.inner() {
                    unsupported.push(UnsupportedFeature::Datatype(dt.name.clone()));
                }
                // Track violations
                if name.starts_with("ay_violation_") {
                    violations.push(name.clone());
                }
            }
            BindingsConstraint::DeclareFun { return_sort, arg_sorts, .. } => {
                // Check sorts for datatypes
                if let BindingsSortInner::Datatype(dt) = return_sort.inner() {
                    unsupported.push(UnsupportedFeature::Datatype(dt.name.clone()));
                }
                for sort in arg_sorts {
                    if let BindingsSortInner::Datatype(dt) = sort.inner() {
                        unsupported.push(UnsupportedFeature::Datatype(dt.name.clone()));
                    }
                }
            }

            // Check assertions for quantifiers/datatypes
            BindingsConstraint::Assert { expr, .. } => {
                check_expr_for_unsupported(expr, &mut unsupported);
            }

            // Other commands are fine
            _ => {}
        }
    }

    ProgramAnalysis { unsupported, detected_logic, violations }
}

/// Recursively check an expression for unsupported features.
fn check_expr_for_unsupported(expr: &BindingsExpr, unsupported: &mut Vec<UnsupportedFeature>) {
    match expr.value() {
        // Quantifiers require fallback
        ExprValue::Forall { .. } | ExprValue::Exists { .. } => {
            if !unsupported.contains(&UnsupportedFeature::Quantifier) {
                unsupported.push(UnsupportedFeature::Quantifier);
            }
        }

        // Datatype operations require fallback
        ExprValue::DatatypeConstructor { datatype_name, .. }
        | ExprValue::DatatypeSelector { datatype_name, .. }
        | ExprValue::DatatypeTester { datatype_name, .. } => {
            let dt_feature = UnsupportedFeature::Datatype(datatype_name.clone());
            if !unsupported.contains(&dt_feature) {
                unsupported.push(dt_feature);
            }
        }

        // Recursively check subexpressions (only operations supported in direct API)
        ExprValue::Not(e)
        | ExprValue::IntNeg(e)
        | ExprValue::RealNeg(e)
        | ExprValue::IntToReal(e) => {
            check_expr_for_unsupported(e, unsupported);
        }

        ExprValue::And(exprs) | ExprValue::Or(exprs) | ExprValue::Distinct(exprs) => {
            for e in exprs {
                check_expr_for_unsupported(e, unsupported);
            }
        }

        // Binary operations supported in direct API - just recursive check
        ExprValue::Xor(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::Eq(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::IntAdd(a, b)
        | ExprValue::IntSub(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntDiv(a, b)
        | ExprValue::IntMod(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::RealAdd(a, b)
        | ExprValue::RealSub(a, b)
        | ExprValue::RealMul(a, b)
        | ExprValue::RealDiv(a, b)
        | ExprValue::RealLt(a, b)
        | ExprValue::RealLe(a, b)
        | ExprValue::RealGt(a, b)
        | ExprValue::RealGe(a, b) => {
            check_expr_for_unsupported(a, unsupported);
            check_expr_for_unsupported(b, unsupported);
        }

        ExprValue::Ite { cond, then_expr, else_expr } => {
            check_expr_for_unsupported(cond, unsupported);
            check_expr_for_unsupported(then_expr, unsupported);
            check_expr_for_unsupported(else_expr, unsupported);
        }

        ExprValue::Select { array, index } => {
            check_expr_for_unsupported(array, unsupported);
            check_expr_for_unsupported(index, unsupported);
        }

        ExprValue::Store { array, index, value } => {
            check_expr_for_unsupported(array, unsupported);
            check_expr_for_unsupported(index, unsupported);
            check_expr_for_unsupported(value, unsupported);
        }

        ExprValue::ConstArray { value, .. } => {
            check_expr_for_unsupported(value, unsupported);
        }

        ExprValue::BvZeroExtend { expr, .. }
        | ExprValue::BvSignExtend { expr, .. }
        | ExprValue::BvExtract { expr, .. } => {
            if !unsupported.contains(&UnsupportedFeature::UnsupportedBvExtend) {
                unsupported.push(UnsupportedFeature::UnsupportedBvExtend);
            }
            check_expr_for_unsupported(expr, unsupported);
        }

        // Overflow checks not yet in direct API
        ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b) => {
            if !unsupported.contains(&UnsupportedFeature::UnsupportedOverflowCheck) {
                unsupported.push(UnsupportedFeature::UnsupportedOverflowCheck);
            }
            check_expr_for_unsupported(a, unsupported);
            check_expr_for_unsupported(b, unsupported);
        }

        ExprValue::BvNegNoOverflow(expr) => {
            if !unsupported.contains(&UnsupportedFeature::UnsupportedOverflowCheck) {
                unsupported.push(UnsupportedFeature::UnsupportedOverflowCheck);
            }
            check_expr_for_unsupported(expr, unsupported);
        }

        // BV operations not in direct API - need SMT-LIB fallback
        ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvSGt(a, b) => {
            if !unsupported.iter().any(|f| matches!(f, UnsupportedFeature::UnsupportedBvOp(_))) {
                unsupported
                    .push(UnsupportedFeature::UnsupportedBvOp("advanced BV ops"));
            }
            check_expr_for_unsupported(a, unsupported);
            check_expr_for_unsupported(b, unsupported);
        }

        ExprValue::BvNeg(a) | ExprValue::BvNot(a) => {
            if !unsupported.iter().any(|f| matches!(f, UnsupportedFeature::UnsupportedBvOp(_))) {
                unsupported.push(UnsupportedFeature::UnsupportedBvOp("bvneg/bvnot"));
            }
            check_expr_for_unsupported(a, unsupported);
        }

        ExprValue::BvConcat(a, b) => {
            if !unsupported.iter().any(|f| matches!(f, UnsupportedFeature::UnsupportedBvOp(_))) {
                unsupported.push(UnsupportedFeature::UnsupportedBvOp("concat"));
            }
            check_expr_for_unsupported(a, unsupported);
            check_expr_for_unsupported(b, unsupported);
        }

        ExprValue::Bv2Int(expr) => {
            if !unsupported.iter().any(|f| matches!(f, UnsupportedFeature::UnsupportedBvOp(_))) {
                unsupported.push(UnsupportedFeature::UnsupportedBvOp("bv2int"));
            }
            check_expr_for_unsupported(expr, unsupported);
        }

        ExprValue::Int2Bv(expr, _width) => {
            if !unsupported.iter().any(|f| matches!(f, UnsupportedFeature::UnsupportedBvOp(_))) {
                unsupported.push(UnsupportedFeature::UnsupportedBvOp("int2bv"));
            }
            check_expr_for_unsupported(expr, unsupported);
        }

        ExprValue::FuncApp { args, .. } => {
            for arg in args {
                check_expr_for_unsupported(arg, unsupported);
            }
        }

        // Constants and variables are always supported
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_)
        | ExprValue::Var { .. } => {}
    }
}
