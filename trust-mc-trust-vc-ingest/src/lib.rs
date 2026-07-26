// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! trust_vc MergeBundle v4 ingest adapter for trust_mc.
//!
//! Translates trust_vc verification artifacts (MergeBundle v4) into ay
//! verification conditions that can be checked by the ay solver backend.
//!
//! This crate implements Phase M2 of the trust_vc-to-trust_mc merge readiness
//! contract (see `designs/2026-03-21-issue-4082-trust_vc-post-parity-landing-zone.md`).

use ay_bindings::{AYProgram, Expr, Sort, constraint::logic};
use std::collections::BTreeMap;
use trust_vc_merge_contract::{
    BroadcastLemmaMeta, FuelAxiomMeta, FuncDeclMeta, MergeBundle, TypedExpr, VarDecl,
};

mod expr_map;
mod sort_map;

pub use expr_map::{DeclaredFunction, MappedExpr};
pub use sort_map::translate_sort;

/// A parsed and sort-mapped trust_vc verification unit ready for ay execution.
#[derive(Debug)]
/// Name mirrors the `trust_vc` tool/IR namespace.
#[allow(non_camel_case_types)]
pub struct trust_vcVerificationUnit {
    pub source_id: String,
    pub variables: Vec<MappedVar>,
    pub functions: Vec<DeclaredFunction>,
    pub func_decls: Vec<DeclaredFunction>,
    pub assumptions: Vec<MappedExpr>,
    pub assertions: Vec<MappedExpr>,
    pub decreases: Vec<MappedExpr>,
    pub triggers: Vec<MappedExpr>,
    pub fuel_axioms: Vec<MappedFuelAxiom>,
    pub broadcast_lemmas: Vec<MappedBroadcastLemma>,
    pub metadata: BTreeMap<String, String>,
}

/// A trust_vc variable declaration mapped to a ay sort.
#[derive(Debug, Clone)]
pub struct MappedVar {
    pub name: String,
    pub sort: Sort,
    pub meta: trust_vc_merge_contract::SortMeta,
}

/// A mapped recursive-function defining axiom from trust_vc v4 metadata.
#[derive(Debug, Clone)]
pub struct MappedFuelAxiom {
    pub function_name: String,
    pub bound_vars: Vec<MappedVar>,
    pub axiom: MappedExpr,
    pub trigger: MappedExpr,
    pub quantified: Expr,
}

/// A mapped broadcast lemma from trust_vc v4 metadata.
#[derive(Debug, Clone)]
pub struct MappedBroadcastLemma {
    pub name: String,
    pub bound_vars: Vec<MappedVar>,
    pub body: MappedExpr,
    pub guard: Option<MappedExpr>,
    pub trigger_groups: Vec<Vec<MappedExpr>>,
    pub group: Option<String>,
    pub quantified: Expr,
}

/// Errors during trust_vc bundle ingestion.
#[derive(Debug, thiserror::Error)]
pub enum IngestError {
    #[error("MergeBundle parse error: {0}")]
    BundleParse(#[from] trust_vc_merge_contract::MergeBundleError),

    #[error("sort mapping error for variable `{var}`: {reason}")]
    SortMapping { var: String, reason: String },

    #[error("expression parse error for `{expr}`: {reason}")]
    ExpressionParse { expr: String, reason: String },

    #[error("unsupported trust_vc expression `{expr}`: {reason}")]
    UnsupportedExpression { expr: String, reason: String },

    #[error("expression sort mismatch for `{expr}`: expected {expected}, got {actual}")]
    ExpressionSortMismatch { expr: String, expected: String, actual: String },

    #[error("function signature mismatch for `{expr}`: {reason}")]
    FunctionSignature { expr: String, reason: String },

    #[error("bundle `{source_id}` does not contain any assertions")]
    MissingAssertions { source_id: String },
}

/// Ingest a trust_vc MergeBundle v4 JSON string into a ay-ready verification unit.
///
/// Parses the bundle, enforces version compatibility, and maps all variable
/// sorts and expressions into typed ay equivalents. Original expression text is
/// retained on each mapped expression for diagnostics and artifact traceability.
pub fn ingest_bundle(json: &str) -> Result<trust_vcVerificationUnit, IngestError> {
    let bundle = MergeBundle::from_json_str(json)?;
    let variables = bundle.variables().iter().map(map_var).collect::<Result<Vec<_>, _>>()?;
    let mut expr_mapper = expr_map::ExprMapper::new(&variables);
    let func_decls =
        bundle.func_decls().iter().map(map_func_decl).collect::<Result<Vec<_>, _>>()?;
    for func_decl in &func_decls {
        expr_mapper.register_function(func_decl.clone())?;
    }
    let assumptions = translate_exprs(&mut expr_mapper, bundle.assumptions())?;
    let assertions = translate_exprs(&mut expr_mapper, bundle.assertions())?;
    let decreases = translate_grouped_exprs(
        &mut expr_mapper,
        bundle.decreases().iter().flat_map(|clause| clause.measures().iter()),
    )?;
    let triggers = translate_grouped_exprs(
        &mut expr_mapper,
        bundle.triggers().iter().flat_map(|group| group.patterns().iter()),
    )?;
    let fuel_axioms = translate_fuel_axioms(&mut expr_mapper, bundle.fuel_axioms())?;
    let broadcast_lemmas = translate_broadcast_lemmas(&mut expr_mapper, bundle.broadcast_lemmas())?;

    Ok(trust_vcVerificationUnit {
        source_id: bundle.source_id().to_string(),
        variables,
        functions: expr_mapper.functions(),
        func_decls,
        assumptions,
        assertions,
        decreases,
        triggers,
        fuel_axioms,
        broadcast_lemmas,
        metadata: bundle.metadata().clone(),
    })
}

fn map_var(decl: &VarDecl) -> Result<MappedVar, IngestError> {
    let sort = translate_sort(decl.sort())
        .map_err(|reason| IngestError::SortMapping { var: decl.name().to_string(), reason })?;
    Ok(MappedVar { name: decl.name().to_string(), sort, meta: decl.sort().clone() })
}

fn map_func_decl(decl: &FuncDeclMeta) -> Result<DeclaredFunction, IngestError> {
    let arg_sorts =
        decl.param_sorts().iter().map(translate_sort).collect::<Result<Vec<_>, _>>().map_err(
            |reason| IngestError::FunctionSignature { expr: decl.name().to_string(), reason },
        )?;
    let return_sort = translate_sort(decl.return_sort()).map_err(|reason| {
        IngestError::FunctionSignature { expr: decl.name().to_string(), reason }
    })?;
    Ok(DeclaredFunction {
        name: decl.name().to_string(),
        param_names: decl.param_names().to_vec(),
        arg_sorts,
        return_sort,
        is_recursive: decl.is_recursive(),
    })
}

fn translate_exprs(
    expr_mapper: &mut expr_map::ExprMapper,
    exprs: &[TypedExpr],
) -> Result<Vec<MappedExpr>, IngestError> {
    translate_grouped_exprs(expr_mapper, exprs.iter())
}

fn translate_grouped_exprs<'a>(
    expr_mapper: &mut expr_map::ExprMapper,
    exprs: impl IntoIterator<Item = &'a TypedExpr>,
) -> Result<Vec<MappedExpr>, IngestError> {
    exprs.into_iter().map(|expr| expr_mapper.translate(expr)).collect()
}

fn translate_fuel_axioms(
    expr_mapper: &mut expr_map::ExprMapper,
    axioms: &[FuelAxiomMeta],
) -> Result<Vec<MappedFuelAxiom>, IngestError> {
    axioms
        .iter()
        .map(|axiom| {
            let bound_vars =
                axiom.bound_vars().iter().map(map_var).collect::<Result<Vec<_>, _>>()?;
            let axiom_expr =
                expr_mapper.translate_with_bound_vars(&bound_vars, axiom.axiom_expr())?;
            let trigger =
                expr_mapper.translate_with_bound_vars(&bound_vars, axiom.trigger_pattern())?;
            let quantified = quantified_forall(
                &bound_vars,
                axiom_expr.expr.clone(),
                vec![vec![trigger.expr.clone()]],
                axiom.axiom_expr().expr(),
            )?;

            Ok(MappedFuelAxiom {
                function_name: axiom.function_name().to_string(),
                bound_vars,
                axiom: axiom_expr,
                trigger,
                quantified,
            })
        })
        .collect()
}

fn translate_broadcast_lemmas(
    expr_mapper: &mut expr_map::ExprMapper,
    lemmas: &[BroadcastLemmaMeta],
) -> Result<Vec<MappedBroadcastLemma>, IngestError> {
    lemmas
        .iter()
        .map(|lemma| {
            let bound_vars =
                lemma.bound_vars().iter().map(map_var).collect::<Result<Vec<_>, _>>()?;
            let body = expr_mapper.translate_with_bound_vars(&bound_vars, lemma.body_expr())?;
            let guard = lemma
                .guard_expr()
                .map(|guard| expr_mapper.translate_with_bound_vars(&bound_vars, guard))
                .transpose()?;
            let trigger_groups = lemma
                .trigger_groups()
                .iter()
                .map(|group| {
                    group
                        .iter()
                        .map(|trigger| expr_mapper.translate_with_bound_vars(&bound_vars, trigger))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            let quantified_body = if let Some(guard) = &guard {
                guard.expr.clone().implies(body.expr.clone())
            } else {
                body.expr.clone()
            };
            let quantified = quantified_forall(
                &bound_vars,
                quantified_body,
                trigger_groups
                    .iter()
                    .map(|group| group.iter().map(|trigger| trigger.expr.clone()).collect())
                    .collect(),
                lemma.body_expr().expr(),
            )?;

            Ok(MappedBroadcastLemma {
                name: lemma.name().to_string(),
                bound_vars,
                body,
                guard,
                trigger_groups,
                group: lemma.group().map(ToOwned::to_owned),
                quantified,
            })
        })
        .collect()
}

fn quantified_forall(
    bound_vars: &[MappedVar],
    body: Expr,
    triggers: Vec<Vec<Expr>>,
    source: &str,
) -> Result<Expr, IngestError> {
    let vars =
        bound_vars.iter().map(|var| (var.name.clone(), var.sort.clone())).collect::<Vec<_>>();
    Expr::try_forall_with_triggers(vars, body, triggers).map_err(|err| {
        IngestError::UnsupportedExpression { expr: source.to_string(), reason: err.to_string() }
    })
}

impl trust_vcVerificationUnit {
    #[must_use]
    pub fn logic(&self) -> &'static str {
        let has_functions = !self.functions.is_empty();
        let has_quantifiers = !self.fuel_axioms.is_empty() || !self.broadcast_lemmas.is_empty();
        let has_arrays = self
            .variables
            .iter()
            .map(|var| &var.sort)
            .chain(self.functions.iter().flat_map(|fun| fun.arg_sorts.iter()))
            .chain(self.functions.iter().map(|fun| &fun.return_sort))
            .any(|sort| sort.is_array() || sort.is_seq());
        let has_bitvecs = self
            .variables
            .iter()
            .map(|var| &var.sort)
            .chain(self.functions.iter().flat_map(|fun| fun.arg_sorts.iter()))
            .chain(self.functions.iter().map(|fun| &fun.return_sort))
            .any(Sort::is_bitvec);
        let has_fp = self
            .variables
            .iter()
            .map(|var| &var.sort)
            .chain(self.functions.iter().flat_map(|fun| fun.arg_sorts.iter()))
            .chain(self.functions.iter().map(|fun| &fun.return_sort))
            .any(Sort::is_floating_point);

        if has_quantifiers || has_arrays || has_fp {
            logic::ALL
        } else if has_bitvecs && has_functions {
            logic::QF_UFBV
        } else if has_bitvecs {
            logic::QF_BV
        } else {
            logic::QF_UF
        }
    }

    pub fn to_program(&self) -> Result<AYProgram, IngestError> {
        if self.assertions.is_empty() {
            return Err(IngestError::MissingAssertions { source_id: self.source_id.clone() });
        }

        let mut program = AYProgram::new();
        program.set_logic(self.logic());
        program.produce_models();

        for variable in &self.variables {
            let _ = program.declare_const(&variable.name, variable.sort.clone());
        }
        for function in &self.functions {
            program.declare_fun(
                &function.name,
                function.arg_sorts.clone(),
                function.return_sort.clone(),
            );
        }
        for fuel_axiom in &self.fuel_axioms {
            program.assert(fuel_axiom.quantified.clone());
        }
        for broadcast_lemma in &self.broadcast_lemmas {
            program.assert(broadcast_lemma.quantified.clone());
        }
        for assumption in &self.assumptions {
            program.assume(assumption.expr.clone());
        }

        let mut violations = Vec::with_capacity(self.assertions.len());
        for (idx, assertion) in self.assertions.iter().enumerate() {
            let violation =
                program.declare_const(format!("ay_violation_trust_vc_assert_{idx}"), Sort::bool());
            program.assert(violation.clone().eq(assertion.expr.clone().not()));
            violations.push(violation);
        }

        program.assert(Expr::or_many(violations.clone()));
        program.check_sat();
        program.get_value(violations);
        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;
    use trust_vc_merge_contract::fixtures;

    #[test]
    fn ingest_representative_fixture_parses_and_maps() {
        let fixture_json = fixtures::read_checked_in_representative_fixture()
            .expect("checked-in fixture should read");
        let unit = ingest_bundle(&fixture_json).expect("representative fixture should ingest");
        assert!(!unit.source_id.is_empty(), "source_id should be non-empty");
        assert_eq!(unit.assumptions.len(), 1, "expected 1 assumption");
        assert_eq!(unit.assertions.len(), 1, "expected 1 assertion");
        assert_eq!(unit.decreases.len(), 1, "expected 1 decreases measure");
        assert_eq!(unit.triggers.len(), 1, "expected 1 trigger pattern");
        assert_eq!(unit.functions.len(), 1, "trigger should infer one UF declaration");

        for var in &unit.variables {
            assert!(!var.name.is_empty(), "variable name should be non-empty");
        }
        assert_eq!(unit.assumptions[0].expr.to_string(), "(= sum_n ((_ zero_extend 32) n))");
        assert_eq!(unit.assertions[0].expr.to_string(), "(bvuge sum_n ((_ zero_extend 32) n))");
        assert_eq!(unit.triggers[0].expr.to_string(), "(sum n)");
    }

    #[test]
    fn ingest_counterexample_fixture_maps_math_int_terms() {
        let fixture_json = fixtures::read_checked_in_representative_counterexample_fixture()
            .expect("checked-in counterexample fixture should read");
        let unit = ingest_bundle(&fixture_json).expect("counterexample fixture should ingest");
        assert_eq!(unit.assumptions.len(), 1, "expected 1 assumption");
        assert_eq!(unit.assertions.len(), 1, "expected 1 assertion");
        assert_eq!(unit.decreases.len(), 1, "expected 1 decreases measure");
        assert_eq!(unit.triggers.len(), 1, "expected 1 trigger pattern");
        assert!(unit.functions.is_empty(), "counterexample fixture should not infer UFs");
        assert_eq!(unit.assumptions[0].expr.to_string(), "(= x 7)");
        assert_eq!(unit.assertions[0].expr.to_string(), "(> x 100)");
        assert!(unit.variables[0].sort.is_int(), "MathInt should map to Int");
    }

    #[test]
    fn representative_program_declares_violation_and_parses_as_smtlib() {
        let fixture_json = fixtures::read_checked_in_representative_fixture()
            .expect("checked-in fixture should read");
        let unit = ingest_bundle(&fixture_json).expect("representative fixture should ingest");
        let program = unit.to_program().expect("program generation should succeed");
        let smt = program.to_string();

        assert!(
            smt.contains("(declare-fun sum ((_ BitVec 32)) (_ BitVec 64))"),
            "expected inferred UF declaration in program: {smt}"
        );
        assert!(
            smt.contains("ay_violation_trust_vc_assert_0"),
            "expected generated trust_vc violation symbol in program: {smt}"
        );

        let commands = parse(&smt).expect("generated SMT-LIB should parse");
        assert!(
            commands.len() >= 8,
            "expected declarations, assertions, check-sat, and get-value; got {commands:?}"
        );
    }

    #[test]
    fn ingest_v4_fixture_preserves_function_and_quantifier_metadata() {
        let fixture_json =
            fixtures::read_checked_in_v4_fixture().expect("checked-in v4 fixture should read");
        let unit = ingest_bundle(&fixture_json).expect("representative v4 fixture should ingest");

        assert_eq!(unit.func_decls.len(), 1, "expected explicit factorial declaration");
        assert_eq!(unit.func_decls[0].name, "factorial");
        assert_eq!(unit.func_decls[0].param_names, vec!["n"]);
        assert!(unit.func_decls[0].is_recursive);
        assert_eq!(unit.fuel_axioms.len(), 1, "expected one fuel axiom");
        assert_eq!(unit.fuel_axioms[0].function_name, "factorial");
        assert_eq!(unit.fuel_axioms[0].bound_vars[0].name, "n");
        assert_eq!(unit.fuel_axioms[0].trigger.expr.to_string(), "(factorial n)");
        assert_eq!(unit.broadcast_lemmas.len(), 1, "expected one broadcast lemma");
        assert_eq!(unit.broadcast_lemmas[0].name, "broadcast_factorial_positive");
        assert_eq!(unit.broadcast_lemmas[0].trigger_groups.len(), 1);
        assert_eq!(unit.broadcast_lemmas[0].trigger_groups[0][0].expr.to_string(), "(factorial n)");
        assert!(
            unit.variables.iter().any(|var| var.sort.is_floating_point()),
            "v4 fixture should preserve FP sort metadata"
        );
        assert!(
            unit.variables.iter().any(|var| var.sort.is_array()),
            "v4 fixture should preserve Array sort metadata"
        );
        assert_eq!(unit.logic(), logic::ALL, "v4 quantified metadata requires non-QF logic");
    }

    #[test]
    fn representative_v4_program_emits_forall_triggers_and_parses_as_smtlib() {
        let fixture_json =
            fixtures::read_checked_in_v4_fixture().expect("checked-in v4 fixture should read");
        let unit = ingest_bundle(&fixture_json).expect("representative v4 fixture should ingest");
        let program = unit.to_program().expect("program generation should succeed");
        let smt = program.to_string();

        assert!(
            smt.contains("(declare-fun factorial ((_ BitVec 64)) (_ BitVec 64))"),
            "expected explicit factorial declaration in program: {smt}"
        );
        assert!(smt.contains("(forall"), "expected quantified v4 metadata in program: {smt}");
        assert!(
            smt.matches(":pattern ((factorial n))").count() >= 2,
            "expected fuel and broadcast trigger metadata in program: {smt}"
        );

        let commands = parse(&smt).expect("generated v4 SMT-LIB should parse");
        assert!(
            commands.len() >= 12,
            "expected declarations, quantified axioms, assertions, check-sat, and get-value; got {commands:?}"
        );
    }
}
