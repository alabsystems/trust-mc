// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AYProgram translation and direct execution.
//!
//! Translates ay_bindings types to ay_dpll API types and executes
//! AYPrograms directly without SMT-LIB serialization.

use std::collections::HashMap;
use std::time::Instant;

use anyhow::{Result, bail};

use ay_bindings::AYProgram;
use ay_bindings::expr::{Expr as BindingsExpr, ExprValue};
use ay_bindings::sort::{Sort as BindingsSort, SortInner as BindingsSortInner};
use ay_dpll::api::{FuncDecl, Logic, Solver, Sort, Term};

use crate::verification_result::{FailedProperties, VerificationStatus};

use super::program_analysis::analyze_program;
use super::{build_properties, run_ay_direct};

/// Convert ay_bindings::Sort to ay_dpll::api::Sort.
///
/// Returns None for Datatype sorts (unsupported in direct path).
pub(super) fn translate_sort(sort: &BindingsSort) -> Option<Sort> {
    match sort.inner() {
        BindingsSortInner::Bool => Some(Sort::Bool),
        BindingsSortInner::Int => Some(Sort::Int),
        BindingsSortInner::Real => Some(Sort::Real),
        BindingsSortInner::BitVec(bv) => Some(Sort::BitVec(bv.width)),
        BindingsSortInner::Array(arr) => {
            let idx = translate_sort(&arr.index_sort)?;
            let elem = translate_sort(&arr.element_sort)?;
            Some(Sort::Array(Box::new(idx), Box::new(elem)))
        }
        // Datatypes and theory-specific sorts not supported in direct path
        BindingsSortInner::Datatype(_)
        | BindingsSortInner::String
        | BindingsSortInner::FloatingPoint(_, _)
        | BindingsSortInner::Uninterpreted(_)
        | BindingsSortInner::RegLan => None,
    }
}

/// Parse logic string to ay_dpll::api::Logic.
pub(super) fn parse_logic(logic_str: &str) -> Option<Logic> {
    match logic_str {
        "QF_LIA" => Some(Logic::QfLia),
        "QF_LRA" => Some(Logic::QfLra),
        "QF_BV" => Some(Logic::QfBv),
        "QF_ABV" => Some(Logic::QfAbv),
        "QF_AUFBV" => Some(Logic::QfAufbv),
        "QF_AUFLIA" => Some(Logic::QfAuflia),
        "QF_AUFLRA" => Some(Logic::QfAuflra),
        "QF_UF" => Some(Logic::QfUf),
        "QF_UFLIA" => Some(Logic::QfUflia),
        "LIA" => Some(Logic::Lia),
        "LRA" => Some(Logic::Lra),
        _ => None,
    }
}

/// Context for translating expressions, maintaining variable/function mappings.
pub(super) struct TranslationContext<'a> {
    solver: &'a mut Solver,
    /// Map from variable names to their Term handles
    vars: HashMap<String, Term>,
    /// Map from function names to their declarations
    funcs: HashMap<String, FuncDecl>,
}

impl<'a> TranslationContext<'a> {
    pub(super) fn new(solver: &'a mut Solver) -> Self {
        Self { solver, vars: HashMap::new(), funcs: HashMap::new() }
    }

    /// Translate a ay_bindings::Expr to a ay_dpll::api::Term.
    pub(super) fn translate_expr(&mut self, expr: &BindingsExpr) -> Result<Term> {
        match expr.value() {
            // Constants
            ExprValue::BoolConst(v) => Ok(self.solver.bool_const(*v)),
            ExprValue::IntConst(v) => Ok(self.solver.int_const_bigint(v)),
            ExprValue::BitVecConst { value, width } => {
                Ok(self.solver.bv_const_bigint(value, *width))
            }
            ExprValue::RealConst(v) => {
                // Convert BigInt to f64 for real constant (Part of #1893)
                // Note: May lose precision for very large integers
                let val: i64 = v
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("real constant {} too large for i64", v))?;
                Ok(self.solver.real_const(val as f64))
            }

            // Variables
            ExprValue::Var { name } => {
                if let Some(term) = self.vars.get(name) {
                    Ok(*term)
                } else {
                    bail!("Undefined variable: {}", name)
                }
            }

            // Boolean operations
            ExprValue::Not(e) => {
                let t = self.translate_expr(e)?;
                Ok(self.solver.not(t))
            }
            ExprValue::And(exprs) => {
                if exprs.is_empty() {
                    return Ok(self.solver.bool_const(true));
                }
                let terms: Vec<Term> =
                    exprs.iter().map(|e| self.translate_expr(e)).collect::<Result<Vec<_>>>()?;
                Ok(self.solver.and_many(&terms))
            }
            ExprValue::Or(exprs) => {
                if exprs.is_empty() {
                    return Ok(self.solver.bool_const(false));
                }
                let terms: Vec<Term> =
                    exprs.iter().map(|e| self.translate_expr(e)).collect::<Result<Vec<_>>>()?;
                Ok(self.solver.or_many(&terms))
            }
            ExprValue::Xor(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                // xor(a, b) = (a or b) and not (a and b)
                let or_term = self.solver.or(ta, tb);
                let and_term = self.solver.and(ta, tb);
                let not_and = self.solver.not(and_term);
                Ok(self.solver.and(or_term, not_and))
            }
            ExprValue::Implies(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.implies(ta, tb))
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                let tc = self.translate_expr(cond)?;
                let tt = self.translate_expr(then_expr)?;
                let te = self.translate_expr(else_expr)?;
                Ok(self.solver.ite(tc, tt, te))
            }

            // Equality and comparison
            ExprValue::Eq(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.eq(ta, tb))
            }
            ExprValue::Distinct(exprs) => {
                if exprs.len() < 2 {
                    return Ok(self.solver.bool_const(true));
                }
                // distinct(a, b, c, ...) = all pairs are not equal
                let terms: Vec<Term> =
                    exprs.iter().map(|e| self.translate_expr(e)).collect::<Result<Vec<_>>>()?;
                let mut constraints = Vec::new();
                for i in 0..terms.len() {
                    for j in i + 1..terms.len() {
                        constraints.push(self.solver.neq(terms[i], terms[j]));
                    }
                }
                Ok(self.solver.and_many(&constraints))
            }

            // Integer arithmetic
            ExprValue::IntAdd(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.add(ta, tb))
            }
            ExprValue::IntSub(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.sub(ta, tb))
            }
            ExprValue::IntMul(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.mul(ta, tb))
            }
            ExprValue::IntDiv(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.int_div(ta, tb))
            }
            ExprValue::IntMod(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.modulo(ta, tb))
            }
            ExprValue::IntNeg(a) => {
                let ta = self.translate_expr(a)?;
                Ok(self.solver.neg(ta))
            }
            ExprValue::IntLt(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.lt(ta, tb))
            }
            ExprValue::IntLe(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.le(ta, tb))
            }
            ExprValue::IntGt(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.gt(ta, tb))
            }
            ExprValue::IntGe(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.ge(ta, tb))
            }

            // Bitvector operations
            ExprValue::BvAdd(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.bvadd(ta, tb))
            }
            ExprValue::BvSub(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.bvsub(ta, tb))
            }
            ExprValue::BvMul(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.bvmul(ta, tb))
            }
            // Supported BV comparisons (exist in ay_dpll::api)
            ExprValue::BvULt(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.bvult(ta, tb))
            }
            ExprValue::BvSLt(a, b) => {
                let ta = self.translate_expr(a)?;
                let tb = self.translate_expr(b)?;
                Ok(self.solver.bvslt(ta, tb))
            }
            // Unsupported BV operations - ay_dpll::api doesn't have these yet
            // Fixes #537 - programs using these should be detected by analyze_program
            ExprValue::BvUDiv(_, _)
            | ExprValue::BvSDiv(_, _)
            | ExprValue::BvURem(_, _)
            | ExprValue::BvSRem(_, _)
            | ExprValue::BvNeg(_)
            | ExprValue::BvNot(_)
            | ExprValue::BvAnd(_, _)
            | ExprValue::BvOr(_, _)
            | ExprValue::BvXor(_, _)
            | ExprValue::BvShl(_, _)
            | ExprValue::BvLShr(_, _)
            | ExprValue::BvAShr(_, _)
            | ExprValue::BvULe(_, _)
            | ExprValue::BvUGt(_, _)
            | ExprValue::BvUGe(_, _)
            | ExprValue::BvSLe(_, _)
            | ExprValue::BvSGt(_, _)
            | ExprValue::BvSGe(_, _)
            | ExprValue::BvZeroExtend { .. }
            | ExprValue::BvSignExtend { .. }
            | ExprValue::BvExtract { .. }
            | ExprValue::BvConcat(_, _)
            | ExprValue::Bv2Int(_)
            | ExprValue::BvAddNoOverflowUnsigned(_, _)
            | ExprValue::BvAddNoOverflowSigned(_, _)
            | ExprValue::BvSubNoUnderflowUnsigned(_, _)
            | ExprValue::BvSubNoOverflowSigned(_, _)
            | ExprValue::BvMulNoOverflowUnsigned(_, _)
            | ExprValue::BvMulNoOverflowSigned(_, _)
            | ExprValue::BvNegNoOverflow(_)
            | ExprValue::BvSdivNoOverflow(_, _) => {
                bail!("Unsupported BV operation - use analyze_program() for fallback detection")
            }

            // Array operations
            ExprValue::Select { array, index } => {
                let ta = self.translate_expr(array)?;
                let ti = self.translate_expr(index)?;
                Ok(self.solver.select(ta, ti))
            }
            ExprValue::Store { array, index, value } => {
                let ta = self.translate_expr(array)?;
                let ti = self.translate_expr(index)?;
                let tv = self.translate_expr(value)?;
                Ok(self.solver.store(ta, ti, tv))
            }
            ExprValue::ConstArray { index_sort, value } => {
                let idx_sort = translate_sort(index_sort)
                    .ok_or_else(|| anyhow::anyhow!("Unsupported sort in const array"))?;
                let tv = self.translate_expr(value)?;
                Ok(self.solver.const_array(idx_sort, tv))
            }

            // Function application (for uninterpreted functions)
            ExprValue::FuncApp { name, args } => {
                if let Some(func) = self.funcs.get(name).cloned() {
                    let arg_terms: Vec<Term> =
                        args.iter().map(|e| self.translate_expr(e)).collect::<Result<Vec<_>>>()?;
                    Ok(self.solver.apply(&func, &arg_terms))
                } else {
                    bail!("Undefined function: {}", name)
                }
            }

            // Real arithmetic - not yet supported in direct execution
            ExprValue::IntToReal(_)
            | ExprValue::RealAdd(_, _)
            | ExprValue::RealSub(_, _)
            | ExprValue::RealMul(_, _)
            | ExprValue::RealDiv(_, _)
            | ExprValue::RealNeg(_)
            | ExprValue::RealLt(_, _)
            | ExprValue::RealLe(_, _)
            | ExprValue::RealGt(_, _)
            | ExprValue::RealGe(_, _) => {
                bail!("Real arithmetic not yet supported in direct execution path")
            }

            // These should have been filtered out by analyze_program
            ExprValue::Forall { .. }
            | ExprValue::Exists { .. }
            | ExprValue::DatatypeConstructor { .. }
            | ExprValue::DatatypeSelector { .. }
            | ExprValue::DatatypeTester { .. }
            | ExprValue::Int2Bv(_, _) => {
                bail!("Unsupported expression type in direct execution path")
            }
        }
    }
}

/// Run AY verification on a AYProgram using direct API (no SMT-LIB serialization).
///
/// This is Phase 2 of #513 - eliminates SMT-LIB file generation and parsing
/// by directly translating AYProgram constraints to AY's native Rust API.
///
/// Uses `ay_bindings::execute_direct` for the core translation and execution.
/// Falls back to the SMT-LIB text path when features aren't supported.
///
/// # REQUIRES
/// - `program` is a valid AYProgram
///
/// # ENSURES
/// - Returns Ok((status, failed_props, properties)) on successful execution
/// - `status` is Success (UNSAT) or Failure (SAT/UNKNOWN)
/// - `properties` contains one entry per ay_violation_* variable found
/// - Falls back to SMT-LIB path for datatypes, CHC commands, and unsupported BV ops
/// - Returns Err on execution failure
pub(crate) fn run_ay_program_direct(
    program: &AYProgram,
    verbose: bool,
) -> Result<(VerificationStatus, FailedProperties, Vec<crate::property_model::Property>)> {
    use ay_bindings::execute_direct::{ExecuteResult, execute};

    let start = Instant::now();

    if verbose {
        println!("[AY-program-direct] Executing {} commands directly...", program.commands().len());
    }

    // Extract violations for property building
    let analysis = analyze_program(program);
    let violations = analysis.violations.clone();

    // Execute using ay_bindings::execute_direct
    let result = execute(program).map_err(|e| anyhow::anyhow!("Direct execution failed: {}", e))?;

    let elapsed = start.elapsed();

    match result {
        ExecuteResult::Verified => {
            if verbose {
                println!("[AY-program-direct] Result: UNSAT (verified) in {:?}", elapsed);
            }
            let properties = build_properties(&violations, VerificationStatus::Success);
            Ok((VerificationStatus::Success, FailedProperties::None, properties))
        }
        ExecuteResult::Counterexample { model } => {
            if verbose {
                println!("[AY-program-direct] Result: SAT (counterexample) in {:?}", elapsed);
                if !model.is_empty() {
                    println!("[AY-program-direct] Model: {:?}", model);
                }
            }
            let properties = build_properties(&violations, VerificationStatus::Failure);
            Ok((VerificationStatus::Failure, FailedProperties::Other, properties))
        }
        ExecuteResult::NeedsFallback(reason) => {
            if verbose {
                println!("[AY-program-direct] Falling back to SMT-LIB path: {}", reason);
            }
            // Fall back to SMT-LIB text-based execution
            let smt_content = program.to_string();
            run_ay_direct(&smt_content, verbose)
        }
        ExecuteResult::Unknown(reason) => {
            if verbose {
                println!("[AY-program-direct] Result: UNKNOWN ({}) in {:?}", reason, elapsed);
            }
            let properties = build_properties(&violations, VerificationStatus::Failure);
            Ok((VerificationStatus::Failure, FailedProperties::Other, properties))
        }
    }
}
