// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed `trust-mc_core::ChcVc` to `ay_chc::ChcProblem` lowering.
//!
//! This module is used by the library-only native CHC/PDR runner. Unsupported
//! expression families fail closed instead of falling back to parsing SMT-LIB
//! text for production proof decisions.
//!
//! The lowering additionally performs the fail-closed Int↔BV signed-bridge
//! elimination (`eliminate_signed_int_bridges`): clause constraints whose
//! `Int2Bv`/`Bv2Nat` bridge atoms provably lie in the equisatisfiable signed
//! fragment are rewritten to pure QF_BV so ay can decide them; every other
//! clause passes through byte-identical.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Display;
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort, SortInner};

use super::{NativeSolveError, NativeSolveResult};

/// Real per-obligation accounting of the exactness of this module's
/// `ChcVc` -> `ay_chc::ChcProblem` lowering.
///
/// INVARIANT (exact-or-reject): every construct this lowering cannot translate
/// exactly returns `Err` (`unsupported_sort` / `unsupported_expr` /
/// `invalid_vc`) instead of dropping it or minting a fresh havoc value, so on
/// a successful lowering all counters are zero. The counters are still
/// threaded as REAL accounting rather than assumed: if a future change adds a
/// lossy fallback (a dropped constraint, a "sound" havoc, an
/// Undef-as-diagnostic-havoc translation), it MUST increment the matching
/// counter here, which automatically suppresses refutation-witness minting
/// (`ChcPdrEncodingConcreteness::ExactEncoding` requires all-zero counts).
///
/// SCOPE: this accounts only for the translation performed by trust_mc on the
/// submitted typed `ChcVc`. It says nothing about how the `ChcVc` itself was
/// produced from source/MIR semantics.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct TypedChcLoweringAccounting {
    /// Constructs dropped by the lowering (exact-or-reject: 0 on success).
    pub(crate) translation_drops: u64,
    /// Values havoc'd by the lowering, incl. "sound" havoc (0 on success).
    pub(crate) havocs: u64,
    /// Undef-as-diagnostic-havoc translations (0 on success; the typed path
    /// consumes an already-encoded `ChcVc`, so no `Undef` instruction lane
    /// exists here at all).
    pub(crate) undef_diagnostic_havocs: u64,
}

impl TypedChcLoweringAccounting {
    /// True iff the lowering performed zero drops and zero havocs of any kind.
    pub(crate) fn is_exact(self) -> bool {
        self.translation_drops == 0 && self.havocs == 0 && self.undef_diagnostic_havocs == 0
    }
}

// Trust: widened `pub(super)` -> `pub(crate)` so the in-crate differential
// soundness oracle (`crate::soundness_oracle`) can drive the EXACT production
// ChcVc -> ChcProblem lowering — proof↔code fidelity requires testing the real
// lowering, not a re-implementation.
#[cfg(test)]
pub(crate) fn lower_obligation(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeSolveResult<ay_chc::ChcProblem> {
    lower_obligation_with_accounting(obligation).map(|(problem, _)| problem)
}

/// Lower a typed obligation and return the lowering-exactness accounting.
///
/// The accounting is derived from the lowering run itself (see
/// [`TypedChcLoweringAccounting`]); with the current exact-or-reject lowering
/// it is all-zero exactly when this function returns `Ok`.
pub(crate) fn lower_obligation_with_accounting(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeSolveResult<(ay_chc::ChcProblem, TypedChcLoweringAccounting)> {
    // Exact-or-reject: no lowering path below performs a drop or a havoc —
    // each unsupported construct is a hard `Err` — so the accounting stays at
    // its zero default. Any future lossy fallback must increment these fields
    // at the point of the fallback.
    let accounting = TypedChcLoweringAccounting::default();
    let mut problem = ay_chc::ChcProblem::new();
    let mut predicates = BTreeMap::new();

    for relation in &obligation.vc.relations {
        let arg_sorts =
            relation.arg_sorts.iter().map(lower_sort).collect::<NativeSolveResult<Vec<_>>>()?;
        let id = problem.declare_predicate(relation.name.clone(), arg_sorts);
        predicates.insert(relation.name.clone(), id);
    }

    for rule in &obligation.vc.rules {
        let head_id = relation_id(&predicates, rule.head.name.as_str())?;
        let head_args = lower_relation_args(&rule.head)?;
        let body = lower_rule_body(&predicates, &rule.body)?;
        // Receipt-lane P0b: eliminate Int↔BV signed-bridge atoms (Int2Bv/Bv2Nat
        // with the sign-decode Ite) into pure QF_BV where the clause provably
        // lies in the equisatisfiable fragment; otherwise the body passes
        // through byte-identical. This runs INSIDE the single production
        // lowering, so the solved problem, the normalized-input identity, and
        // the fresh replay-validated problem are always the same rewritten
        // problem. See `eliminate_signed_int_bridges` for the full soundness
        // argument (rules R1–R7).
        let body = eliminate_signed_int_bridges(body, &head_args);
        problem.add_clause(ay_chc::HornClause::new(
            body,
            ay_chc::ClauseHead::Predicate(head_id, head_args),
        ));
    }

    let target = obligation.query_target();
    let target_id = relation_id(&predicates, target)?;
    let target_predicate =
        problem.get_predicate(target_id).ok_or_else(|| invalid_vc("query target disappeared"))?;
    if target_predicate.arity() != 0 {
        return Err(invalid_vc(format!(
            "native typed CHC query target `{target}` has arity {}, but ay-chc query clauses \
             require a nullary target",
            target_predicate.arity()
        )));
    }
    problem.add_clause(ay_chc::HornClause::query(ay_chc::ClauseBody::predicates_only(vec![(
        target_id,
        Vec::new(),
    )])));

    Ok((problem, accounting))
}

fn lower_rule_body(
    predicates: &BTreeMap<String, ay_chc::PredicateId>,
    body: &trust_mc_core::RuleBody,
) -> NativeSolveResult<ay_chc::ClauseBody> {
    let mut body_predicates = Vec::new();
    if let Some(relation) = &body.relation {
        body_predicates.push((
            relation_id(predicates, relation.name.as_str())?,
            lower_relation_args(relation)?,
        ));
    }

    let constraints =
        body.constraints.iter().map(lower_expr).collect::<NativeSolveResult<Vec<_>>>()?;
    let constraint =
        if constraints.is_empty() { None } else { Some(ay_chc::ChcExpr::and_vec(constraints)) };

    Ok(ay_chc::ClauseBody::new(body_predicates, constraint))
}

fn lower_relation_args(
    relation: &trust_mc_core::RelationApp,
) -> NativeSolveResult<Vec<ay_chc::ChcExpr>> {
    relation.args.iter().map(lower_expr).collect()
}

fn relation_id(
    predicates: &BTreeMap<String, ay_chc::PredicateId>,
    name: &str,
) -> NativeSolveResult<ay_chc::PredicateId> {
    predicates
        .get(name)
        .copied()
        .ok_or_else(|| invalid_vc(format!("relation `{name}` was not declared")))
}

fn lower_sort(sort: &Sort) -> NativeSolveResult<ay_chc::ChcSort> {
    match sort.inner() {
        SortInner::Bool => Ok(ay_chc::ChcSort::Bool),
        SortInner::BitVec(bitvec) => Ok(ay_chc::ChcSort::BitVec(bitvec.width)),
        SortInner::Int => Ok(ay_chc::ChcSort::Int),
        SortInner::Real => Ok(ay_chc::ChcSort::Real),
        SortInner::Array(array) => Ok(ay_chc::ChcSort::Array(
            Box::new(lower_sort(&array.index_sort)?),
            Box::new(lower_sort(&array.element_sort)?),
        )),
        SortInner::Datatype(datatype) => {
            let constructors = datatype
                .constructors
                .iter()
                .map(|constructor| {
                    let selectors = constructor
                        .fields
                        .iter()
                        .map(|field| {
                            Ok(ay_chc::ChcDtSelector {
                                name: field.name.clone(),
                                sort: lower_sort(&field.sort)?,
                            })
                        })
                        .collect::<NativeSolveResult<Vec<_>>>()?;
                    Ok(ay_chc::ChcDtConstructor { name: constructor.name.clone(), selectors })
                })
                .collect::<NativeSolveResult<Vec<_>>>()?;
            Ok(ay_chc::ChcSort::Datatype {
                name: datatype.name.clone(),
                constructors: Arc::new(constructors),
            })
        }
        SortInner::Uninterpreted(name) => Ok(ay_chc::ChcSort::Uninterpreted(name.clone())),
        SortInner::String
        | SortInner::FloatingPoint(_, _)
        | SortInner::RegLan
        | SortInner::Seq(_) => Err(unsupported_sort(sort)),
        _ => Err(unsupported_sort(sort)),
    }
}

/// Memoization cache for [`lower_expr`], keyed by the allocation identity of each
/// shared `ExprValue` node. `Expr` is `{ sort, value: Arc<ExprValue> }` and
/// `Expr::value()` returns `&*value`, so the address is stable and is shared by every
/// `Expr` handle that clones the same node.
type LowerCache = HashMap<*const ExprValue, Arc<ay_chc::ChcExpr>>;

thread_local! {
    /// Per-top-level-lowering identity cache. `None` between lowerings; the outermost
    /// `lower_expr` call installs it and a drop guard clears it (even on early return
    /// or panic), so the raw-pointer keys can never outlive — or alias a freed —
    /// `ExprValue`. The whole input DAG is borrowed for the duration of a lowering, so
    /// every key stays valid while it is in the cache.
    static LOWER_CACHE: RefCell<Option<LowerCache>> = const { RefCell::new(None) };
}

/// Lower one `ay_bindings::Expr` to an `ay_chc::ChcExpr`.
///
/// `ay_bindings::Expr` is a *shared* `Arc<ExprValue>` DAG: a value built by repeated
/// self-combination (`v = v + v`, N deep) has only `O(N)` distinct nodes but `O(2^N)`
/// root-to-leaf paths. The structural recursion in `lower_expr_node` visits children
/// unconditionally, so without memoization it re-lowers each shared subterm once per
/// path — `O(2^N)` `ChcExpr` nodes, which exhausts RAM + swap (an OOM that can take the
/// machine down). Memoizing by node identity makes each distinct node lower exactly
/// once and lets shared `Arc<ChcExpr>` subterms be reused, so lowering is `O(N)`.
/// Sound because `lower_expr_node` is a pure function of its node (no external
/// context): two occurrences of the same node always lower identically.
fn lower_expr(expr: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    /// Clears the thread-local cache when the outermost `lower_expr` call returns, so
    /// identity keys never persist past the lowering that owns the live `Expr`s.
    struct CacheGuard(bool);
    impl Drop for CacheGuard {
        fn drop(&mut self) {
            if self.0 {
                LOWER_CACHE.with(|cache| *cache.borrow_mut() = None);
            }
        }
    }

    // Install the cache on the outermost call; nested calls reuse it.
    let _guard = LOWER_CACHE.with(|cache| {
        let mut slot = cache.borrow_mut();
        if slot.is_none() {
            *slot = Some(LowerCache::new());
            CacheGuard(true)
        } else {
            CacheGuard(false)
        }
    });

    let key: *const ExprValue = expr.value();
    if let Some(cached) =
        LOWER_CACHE.with(|cache| cache.borrow().as_ref().and_then(|map| map.get(&key).cloned()))
    {
        return Ok((*cached).clone());
    }

    let lowered = Arc::new(lower_expr_node(expr)?);
    LOWER_CACHE.with(|cache| {
        if let Some(map) = cache.borrow_mut().as_mut() {
            map.insert(key, Arc::clone(&lowered));
        }
    });
    Ok((*lowered).clone())
}

fn lower_expr_node(expr: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    match expr.value() {
        ExprValue::BoolConst(value) => Ok(ay_chc::ChcExpr::Bool(*value)),
        ExprValue::BitVecConst { value, width } => {
            Ok(ay_chc::ChcExpr::BitVec(parse_u128(value, "bitvector constant")?, *width))
        }
        ExprValue::IntConst(value) => lower_int_constant(value),
        ExprValue::RealConst(value) => {
            Ok(ay_chc::ChcExpr::Real(parse_i64(value, "real constant")?, 1))
        }
        ExprValue::Var { name } => {
            Ok(ay_chc::ChcExpr::var(ay_chc::ChcVar::new(name.clone(), lower_sort(expr.sort())?)))
        }
        ExprValue::Not(inner) => Ok(ay_chc::ChcExpr::not(lower_expr(inner)?)),
        ExprValue::And(args) => lower_nary(args, ay_chc::ChcExpr::and_vec),
        ExprValue::Or(args) => lower_nary(args, ay_chc::ChcExpr::or_vec),
        ExprValue::Xor(lhs, rhs) => lower_binary(ay_chc::ChcOp::Ne, lhs, rhs),
        ExprValue::Implies(lhs, rhs) => {
            Ok(ay_chc::ChcExpr::implies(lower_expr(lhs)?, lower_expr(rhs)?))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => Ok(ay_chc::ChcExpr::ite(
            lower_expr(cond)?,
            lower_expr(then_expr)?,
            lower_expr(else_expr)?,
        )),
        ExprValue::Eq(lhs, rhs) => lower_binary(ay_chc::ChcOp::Eq, lhs, rhs),
        ExprValue::Distinct(args) if args.len() == 2 => {
            lower_binary(ay_chc::ChcOp::Ne, &args[0], &args[1])
        }
        ExprValue::Distinct(args) => {
            let mut disequalities = Vec::new();
            for left in 0..args.len() {
                for right in (left + 1)..args.len() {
                    disequalities.push(op2(
                        ay_chc::ChcOp::Ne,
                        lower_expr(&args[left])?,
                        lower_expr(&args[right])?,
                    ));
                }
            }
            Ok(ay_chc::ChcExpr::and_vec(disequalities))
        }
        ExprValue::BvAdd(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvAdd, lhs, rhs),
        ExprValue::BvSub(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSub, lhs, rhs),
        ExprValue::BvMul(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvMul, lhs, rhs),
        ExprValue::BvUDiv(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvUDiv, lhs, rhs),
        ExprValue::BvSDiv(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSDiv, lhs, rhs),
        ExprValue::BvURem(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvURem, lhs, rhs),
        ExprValue::BvSRem(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSRem, lhs, rhs),
        ExprValue::BvNeg(inner) => lower_unary(ay_chc::ChcOp::BvNeg, inner),
        ExprValue::BvNot(inner) => lower_unary(ay_chc::ChcOp::BvNot, inner),
        ExprValue::BvAnd(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvAnd, lhs, rhs),
        ExprValue::BvOr(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvOr, lhs, rhs),
        ExprValue::BvXor(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvXor, lhs, rhs),
        ExprValue::BvShl(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvShl, lhs, rhs),
        ExprValue::BvLShr(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvLShr, lhs, rhs),
        ExprValue::BvAShr(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvAShr, lhs, rhs),
        ExprValue::BvULt(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvULt, lhs, rhs),
        ExprValue::BvULe(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvULe, lhs, rhs),
        ExprValue::BvUGt(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvUGt, lhs, rhs),
        ExprValue::BvUGe(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvUGe, lhs, rhs),
        ExprValue::BvSLt(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSLt, lhs, rhs),
        ExprValue::BvSLe(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSLe, lhs, rhs),
        ExprValue::BvSGt(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSGt, lhs, rhs),
        ExprValue::BvSGe(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvSGe, lhs, rhs),
        ExprValue::BvZeroExtend { expr, extra_bits } => {
            lower_unary(ay_chc::ChcOp::BvZeroExtend(*extra_bits), expr)
        }
        ExprValue::BvSignExtend { expr, extra_bits } => {
            lower_unary(ay_chc::ChcOp::BvSignExtend(*extra_bits), expr)
        }
        ExprValue::BvExtract { expr, high, low } => {
            lower_unary(ay_chc::ChcOp::BvExtract(*high, *low), expr)
        }
        ExprValue::BvConcat(lhs, rhs) => lower_binary(ay_chc::ChcOp::BvConcat, lhs, rhs),
        ExprValue::IntAdd(lhs, rhs) => lower_binary(ay_chc::ChcOp::Add, lhs, rhs),
        ExprValue::IntSub(lhs, rhs) => lower_binary(ay_chc::ChcOp::Sub, lhs, rhs),
        ExprValue::IntMul(lhs, rhs) => lower_binary(ay_chc::ChcOp::Mul, lhs, rhs),
        ExprValue::IntDiv(lhs, rhs) => lower_binary(ay_chc::ChcOp::Div, lhs, rhs),
        ExprValue::IntMod(lhs, rhs) => lower_binary(ay_chc::ChcOp::Mod, lhs, rhs),
        ExprValue::IntNeg(inner) => lower_unary(ay_chc::ChcOp::Neg, inner),
        ExprValue::IntLt(lhs, rhs) => lower_binary(ay_chc::ChcOp::Lt, lhs, rhs),
        ExprValue::IntLe(lhs, rhs) => lower_binary(ay_chc::ChcOp::Le, lhs, rhs),
        ExprValue::IntGt(lhs, rhs) => lower_binary(ay_chc::ChcOp::Gt, lhs, rhs),
        ExprValue::IntGe(lhs, rhs) => lower_binary(ay_chc::ChcOp::Ge, lhs, rhs),
        ExprValue::RealAdd(lhs, rhs) => lower_binary(ay_chc::ChcOp::Add, lhs, rhs),
        ExprValue::RealSub(lhs, rhs) => lower_binary(ay_chc::ChcOp::Sub, lhs, rhs),
        ExprValue::RealMul(lhs, rhs) => lower_binary(ay_chc::ChcOp::Mul, lhs, rhs),
        ExprValue::RealDiv(lhs, rhs) => lower_binary(ay_chc::ChcOp::Div, lhs, rhs),
        ExprValue::RealNeg(inner) => lower_unary(ay_chc::ChcOp::Neg, inner),
        ExprValue::RealLt(lhs, rhs) => lower_binary(ay_chc::ChcOp::Lt, lhs, rhs),
        ExprValue::RealLe(lhs, rhs) => lower_binary(ay_chc::ChcOp::Le, lhs, rhs),
        ExprValue::RealGt(lhs, rhs) => lower_binary(ay_chc::ChcOp::Gt, lhs, rhs),
        ExprValue::RealGe(lhs, rhs) => lower_binary(ay_chc::ChcOp::Ge, lhs, rhs),
        ExprValue::Select { array, index } => lower_binary(ay_chc::ChcOp::Select, array, index),
        ExprValue::Store { array, index, value } => {
            Ok(ay_chc::ChcExpr::store(lower_expr(array)?, lower_expr(index)?, lower_expr(value)?))
        }
        ExprValue::ConstArray { index_sort, value } => {
            Ok(ay_chc::ChcExpr::const_array(lower_sort(index_sort)?, lower_expr(value)?))
        }
        ExprValue::FuncApp { name, args } => {
            Ok(ay_chc::ChcExpr::FuncApp(name.clone(), lower_sort(expr.sort())?, lower_exprs(args)?))
        }
        ExprValue::DatatypeConstructor { constructor_name, args, .. } => {
            Ok(ay_chc::ChcExpr::FuncApp(
                constructor_name.clone(),
                lower_sort(expr.sort())?,
                lower_exprs(args)?,
            ))
        }
        ExprValue::DatatypeSelector { selector_name, expr: inner, .. } => {
            Ok(ay_chc::ChcExpr::FuncApp(
                selector_name.clone(),
                lower_sort(expr.sort())?,
                vec![Arc::new(lower_expr(inner)?)],
            ))
        }
        ExprValue::Bv2Int(inner) => lower_unary(ay_chc::ChcOp::Bv2Nat, inner),
        ExprValue::Int2Bv(inner, width) => lower_unary(ay_chc::ChcOp::Int2Bv(*width), inner),
        // Trust Gap 3 (build #29): bit-vector overflow PREDICATES. ay-chc has no
        // native overflow op, so expand each into its EXACT two's-complement
        // definition. Each predicate is TRUE iff the op does NOT overflow (see
        // ay-bindings `test_bv.rs`: "returns true if no overflow"). The
        // expansions are equisatisfiable, so they never false-PROVE or false-FAIL.
        ExprValue::BvSdivNoOverflow(lhs, rhs) => lower_no_overflow_sdiv(lhs, rhs),
        ExprValue::BvNegNoOverflow(inner) => lower_no_overflow_neg(inner),
        ExprValue::BvSubNoUnderflowUnsigned(lhs, rhs) => lower_no_underflow_sub_unsigned(lhs, rhs),
        ExprValue::BvAddNoOverflowUnsigned(lhs, rhs) => lower_no_overflow_add_unsigned(lhs, rhs),
        ExprValue::BvAddNoOverflowSigned(lhs, rhs) => {
            lower_no_overflow_addsub_signed(ay_chc::ChcOp::BvAdd, lhs, rhs)
        }
        ExprValue::BvSubNoOverflowSigned(lhs, rhs) => {
            lower_no_overflow_addsub_signed(ay_chc::ChcOp::BvSub, lhs, rhs)
        }
        ExprValue::BvMulNoOverflowUnsigned(lhs, rhs) => lower_no_overflow_mul_unsigned(lhs, rhs),
        ExprValue::BvMulNoOverflowSigned(lhs, rhs) => lower_no_overflow_mul_signed(lhs, rhs),
        other => Err(unsupported_expr(other)),
    }
}

fn lower_exprs(args: &[Expr]) -> NativeSolveResult<Vec<Arc<ay_chc::ChcExpr>>> {
    args.iter().map(|arg| lower_expr(arg).map(Arc::new)).collect()
}

fn lower_nary(
    args: &[Expr],
    build: impl FnOnce(Vec<ay_chc::ChcExpr>) -> ay_chc::ChcExpr,
) -> NativeSolveResult<ay_chc::ChcExpr> {
    let lowered = args.iter().map(lower_expr).collect::<NativeSolveResult<Vec<_>>>()?;
    Ok(build(lowered))
}

fn lower_unary(op: ay_chc::ChcOp, inner: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    Ok(ay_chc::ChcExpr::Op(op, vec![Arc::new(lower_expr(inner)?)]))
}

fn lower_binary(op: ay_chc::ChcOp, lhs: &Expr, rhs: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    Ok(op2(op, lower_expr(lhs)?, lower_expr(rhs)?))
}

fn op2(op: ay_chc::ChcOp, lhs: ay_chc::ChcExpr, rhs: ay_chc::ChcExpr) -> ay_chc::ChcExpr {
    ay_chc::ChcExpr::Op(op, vec![Arc::new(lhs), Arc::new(rhs)])
}

fn op1(op: ay_chc::ChcOp, inner: ay_chc::ChcExpr) -> ay_chc::ChcExpr {
    ay_chc::ChcExpr::Op(op, vec![Arc::new(inner)])
}

// ===== Int↔BV signed-bridge elimination (receipt-lane P0b) ==================
//
// The compiler's typed postcondition VCs for signed machine arithmetic mix an
// Int-sorted hypothesis (range facts, guard defs) with BV-encoded operations
// bridged through `Int2Bv(w)`/`Bv2Nat` and the two's-complement sign-decode
// Ite. ay's SMT context cannot decide that mixed Int+bridge theory within the
// production budget (observed: UNDECIDED at 60s), while the same query with
// the bridges eliminated into pure QF_BV decides in milliseconds. This pass
// rewrites each clause constraint into pure QF_BV when — and ONLY when — the
// clause provably lies in the equisatisfiable fragment below; on ANY node or
// shape outside the fragment the clause is left byte-identical, so today's
// behavior is preserved exactly for everything else.
//
// Rewrite rules (equisatisfiability argument per rule):
//
//   R1 (signed var image). Every Int variable v that is either
//       (a) window-bounded: asserted conjunct facts pin v into the signed
//           window [-2^(w-1), 2^(w-1)-1], or
//       (b) decode-defined: an asserted conjunct is the signed bv2nat-decode
//           defining v — either the Bool-level R5 Ite or an equality against
//           the R5t decode TERM,
//     ("asserted conjunct" = a leaf of the constraint's top-level `And` TREE;
//      see `top_level_conjuncts`, which flattens nested `And` and descends
//      through nothing else, so a conjunct under `Or`/`Not`/`Ite` — which is
//      NOT asserted — can never grant a window.)
//     is replaced by a BitVec(w) variable of the SAME NAME under the signed
//     (two's-complement) interpretation v = sbv(v_bv). SOUND because sbv is a
//     BIJECTION between BitVec(w) patterns and the integer window
//     [-2^(w-1), 2^(w-1)-1]: it is total (every pattern decodes), injective
//     (distinct patterns decode to distinct integers — the decode map
//     p ↦ p < 2^(w-1) ? p : p - 2^w is strictly monotone on each half and the
//     halves' images are disjoint), and surjective onto the window (every
//     window integer has a unique w-bit two's-complement pattern). Case (a)
//     facts guarantee v's value lies in the window in EVERY model of the
//     constraint; case (b) forces v = sbv(W) for the decoded BV term W
//     (see R5), which lies in the window by construction. Hence every Int
//     model restricts to window values on rewritten vars and maps to exactly
//     one BV model, and every BV model decodes to exactly one Int model — the
//     two constraint versions are equisatisfiable (in fact their model sets
//     correspond bijectively, identity on all untouched variables).
//   R2 (constant image). An Int literal c inside a rewritten atom must lie in
//     the window and becomes the BitVec(w) literal `c mod 2^w` (its
//     two's-complement pattern). Exact: sbv(c mod 2^w) = c for window c.
//     Out-of-window literals fail the whole clause closed.
//   R3 (comparisons). Int Lt/Le/Gt/Ge over rewritten operands become the
//     SIGNED BV comparisons BvSLt/BvSLe/BvSGt/BvSGe; Eq/Ne stay Eq/Ne at
//     BitVec(w). Exact because bvslt/bvsle compare precisely the sbv values
//     of their operands (SMT-LIB definition) and sbv is injective (for Eq/Ne).
//   R4 (bridge collapse). `Int2Bv(w)(t)`:
//       - t an admissible Int var v: the image is v_bv itself, because
//         int2bv_w is reduction mod 2^w and int2bv_w(sbv(p)) = p for every
//         w-bit pattern p (sbv(p) ≡ p (mod 2^w)).
//       - t an Int literal c: the image is the literal `c mod 2^w`, exactly
//         the SMT-LIB value of int2bv_w(c) (no window requirement — int2bv is
//         total mod-2^w).
//     Pure BV operators between images (BvSub, BvExtract, ...) are kept
//     unchanged: their operands evaluate to identical patterns in the
//     corresponding models, so the terms evaluate identically.
//   R5 (signed-decode collapse). The decode shape
//         Ite(Eq(#b1, BvExtract(w-1,w-1)(W)),
//             Eq(Sub(Bv2Nat(W), 2^w), v),
//             Eq(Bv2Nat(W), v))
//     with v an admissible Int var and W a BV(w) term is rewritten to
//         Ite(Eq(#b1, BvExtract(w-1,w-1)(W')), Eq(W', v_bv), Eq(W', v_bv))
//     (W' = rewritten W; the Ite/BvExtract skeleton and operand orders are
//     kept). EXACT per branch under its guard: when the sign bit of W is set,
//     bv2nat(W) ∈ [2^(w-1), 2^w-1], so bv2nat(W) - 2^w = sbv(W) and the
//     branch asserts v = sbv(W) ⇔ v_bv = W (sbv injective, v = sbv(v_bv));
//     when the sign bit is clear, bv2nat(W) = sbv(W) ∈ [0, 2^(w-1)-1] and the
//     branch again asserts v = sbv(W) ⇔ v_bv = W. Both branches therefore
//     rewrite to the same BV equality, guarded by the (preserved) sign test —
//     the Ite is pointwise equivalent to its rewritten form in every
//     corresponding model pair. Bv2Nat is admitted ONLY inside this matched
//     shape; a stray Bv2Nat fails the clause closed.
//   R5t (signed-decode TERM collapse). The PRODUCER image of a wrap-exact
//     signed conversion is `ay_bindings::Expr::bv2int_signed`, an Int-sorted
//     TERM (not a Bool-level Ite of equalities):
//         Ite(Eq(BvExtract(w-1,w-1)(W), #b1), Sub(Bv2Nat(W), 2^w), Bv2Nat(W))
//     Its value is by definition the two's-complement decode sbv(W), so it
//     rewrites to `W` itself — EXACT and unconditional, since the rewriter's
//     Int-term invariant asks only for an image `t'` with sbv(t') = t. (Both
//     the R5 and R5t forms are matched: the TERM form is what this lowering
//     sees, and the Bool-level R5 form is what ay's downstream clause
//     normalizer produces when it lifts the Ite out of its defining equality.)
//     R1(b) is correspondingly satisfied by a top-level conjunct
//     `Eq(v, <R5t decode>)`: it pins v = sbv(W), which lies in the window by
//     construction. The branch order is pinned to the producer's; the
//     complement (`bvsge` guard, swapped branches) is NOT matched.
//   R6 (window facts). The R1(a) range facts themselves rewrite through R3
//     into signed-BV tautologies (e.g. BvSGe(v_bv, min-pattern)) — true in
//     every BV model, exactly as their Int originals are true for window
//     values. They are kept, not dropped, so the conjunct list keeps its
//     arity and order.
//   R7 (Bool structure). Bool literals, Bool vars, Not/And/Or/Implies/Iff,
//     Bool equalities (guard-definition equations) and Bool Ites keep their
//     shape with rewritten children — truth-functional, so exactness lifts
//     pointwise from the atoms.
//
// Clause-level soundness: the rewrite touches ONLY the clause constraint.
// Rewritten variables are required not to occur in the clause's head or body
// predicate arguments (checked; else fail closed), so the set of derivable
// head instantiations is preserved under the R1 model bijection (which is the
// identity on every untouched variable). This is a pre-solve transformation
// of the lowered `ChcProblem` only — no verdict-layer or authority changes.
//
// Fail-closed gates (any miss leaves the clause byte-identical):
//   G0  at least one bridge node (`Int2Bv`/`Bv2Nat`) is present;
//   G1  all `Int2Bv` widths agree on a single width w, 1 <= w <= 126, and
//       every decode shape matches that width (mixed widths fail);
//   G2  every Int variable reached by the translation is R1-admissible;
//   G3  no admissible name also occurs with a non-Int sort in the constraint
//       (the rewrite would merge two distinct variables), and no admissible
//       name occurs in head/body predicate arguments;
//   G4  every reached node is inside the R2–R7 fragment (no Int arithmetic
//       outside the matched decode, no arrays/reals/uninterpreted functions,
//       no stray Bv2Nat, no out-of-window Int literal).

/// Apply the signed Int↔BV bridge elimination to one lowered clause body.
///
/// Returns the body unchanged (byte-identical constraint) unless the whole
/// constraint rewrites inside the proven fragment; see the module-section
/// comment above for rules R1–R7 and gates G0–G4.
fn eliminate_signed_int_bridges(
    body: ay_chc::ClauseBody,
    head_args: &[ay_chc::ChcExpr],
) -> ay_chc::ClauseBody {
    let Some(constraint) = body.constraint.as_ref() else {
        return body;
    };
    match rewrite_bridged_constraint(constraint, &body.predicates, head_args) {
        Some(rewritten) => ay_chc::ClauseBody::new(body.predicates, Some(rewritten)),
        None => body,
    }
}

fn rewrite_bridged_constraint(
    constraint: &ay_chc::ChcExpr,
    body_predicates: &[(ay_chc::PredicateId, Vec<ay_chc::ChcExpr>)],
    head_args: &[ay_chc::ChcExpr],
) -> Option<ay_chc::ChcExpr> {
    // G0/G1: bridge presence and a single consistent width, derived from the
    // Int2Bv indices present (decode shapes are validated against it below).
    let mut widths = BTreeSet::new();
    let mut saw_bridge = false;
    collect_bridge_widths(constraint, &mut widths, &mut saw_bridge);
    if !saw_bridge {
        return None;
    }
    let mut width_iter = widths.iter();
    let (Some(&width), None) = (width_iter.next(), width_iter.next()) else {
        // No Int2Bv at all (stray Bv2Nat) or mixed widths: fail closed.
        return None;
    };
    // Bounds keep 2^w and -2^(w-1) inside i128 arithmetic below.
    if !(1..=126).contains(&width) {
        return None;
    }

    // R1 admissibility from TOP-LEVEL conjunct facts only: nested occurrences
    // are not asserted and must not grant a window.
    let conjuncts = top_level_conjuncts(constraint);
    let mut admissible: BTreeSet<String> = BTreeSet::new();
    for conjunct in &conjuncts {
        // R1(b), Bool-level decode form: `Ite(sign, v = …, v = …)`.
        if let Some(parts) = match_signed_decode(conjunct, width) {
            admissible.insert(parts.var_name.to_string());
        }
        // R1(b), TERM decode form (the producer image): `v = <decode term>`.
        if let Some(name) = signed_decode_definition_var(conjunct, width) {
            admissible.insert(name.to_string());
        }
    }
    let mut bounds: BTreeMap<String, (Option<i128>, Option<i128>)> = BTreeMap::new();
    for conjunct in &conjuncts {
        record_conjunct_bound(conjunct, &mut bounds);
    }
    let window_min = -(1i128 << (width - 1));
    let window_max = (1i128 << (width - 1)) - 1;
    for (name, (lo, hi)) in &bounds {
        if let (Some(lo), Some(hi)) = (lo, hi) {
            if *lo >= window_min && *hi <= window_max {
                admissible.insert(name.clone());
            }
        }
    }

    // G3: an admissible name occurring with a non-Int sort anywhere in the
    // constraint, or occurring at all in head/body predicate arguments, would
    // be captured/merged by the re-sorting — fail closed.
    let mut constraint_var_sorts: BTreeMap<String, BTreeSet<ay_chc::ChcSort>> = BTreeMap::new();
    collect_var_sorts(constraint, &mut constraint_var_sorts);
    for name in &admissible {
        if constraint_var_sorts
            .get(name)
            .is_some_and(|sorts| sorts.iter().any(|sort| *sort != ay_chc::ChcSort::Int))
        {
            return None;
        }
    }
    let mut argument_var_sorts: BTreeMap<String, BTreeSet<ay_chc::ChcSort>> = BTreeMap::new();
    for (_, args) in body_predicates {
        for arg in args {
            collect_var_sorts(arg, &mut argument_var_sorts);
        }
    }
    for arg in head_args {
        collect_var_sorts(arg, &mut argument_var_sorts);
    }
    if admissible.iter().any(|name| argument_var_sorts.contains_key(name)) {
        return None;
    }

    // G2/G4 are enforced by the translation itself: any Int var outside
    // `admissible` and any node outside the R2-R7 fragment returns None.
    let rewriter = BridgeRewriter {
        width,
        window_min,
        window_max,
        admissible: &admissible,
        memo: RefCell::new(HashMap::new()),
    };
    match constraint {
        ay_chc::ChcExpr::Op(ay_chc::ChcOp::And, args) => {
            let rewritten =
                args.iter().map(|arg| rewriter.rewrite_arc(arg)).collect::<Option<Vec<_>>>()?;
            Some(ay_chc::ChcExpr::Op(
                ay_chc::ChcOp::And,
                rewritten.into_iter().map(Arc::new).collect(),
            ))
        }
        single => rewriter.rewrite_node(single),
    }
}

/// Asserted-fact view of a clause constraint: the leaves of its top-level
/// conjunction TREE, flattened through nested `And` nodes.
///
/// SOUND (R1 precondition discovery): if `A ∧ B` holds in a model then both `A`
/// and `B` hold, so by induction every leaf reachable from the root through
/// `And` nodes only is asserted in EVERY model of the constraint. The walk
/// therefore descends through `And` and nothing else — a conjunct sitting under
/// `Or`/`Not`/`Ite` is NOT asserted and must never grant a window (that would
/// be the one way this scan could manufacture a false admissibility).
///
/// Flattening is load-bearing, not cosmetic: the production typed lowering
/// emits a deep LEFT-NESTED BINARY `And` tree (the compiler's payload builds
/// `a.and(b)` pairwise), so a non-flattening scan sees only the root's two
/// children and misses every range fact and definition below them. ay's own
/// `add_clause` constant-folder later flattens the same tree, but that runs
/// AFTER this lowering, so we cannot rely on it here.
///
/// Iterative (explicit stack): these trees are as deep as the conjunct count,
/// so a structural recursion would risk blowing the stack on large bodies.
fn top_level_conjuncts(constraint: &ay_chc::ChcExpr) -> Vec<&ay_chc::ChcExpr> {
    let mut conjuncts = Vec::new();
    let mut stack = vec![constraint];
    while let Some(node) = stack.pop() {
        match node {
            ay_chc::ChcExpr::Op(ay_chc::ChcOp::And, args) => {
                // Push reversed so the flattened order matches source order.
                for arg in args.iter().rev() {
                    stack.push(arg.as_ref());
                }
            }
            leaf => conjuncts.push(leaf),
        }
    }
    conjuncts
}

/// Structural children of a `ChcExpr` node (for the fragment-neutral walks).
fn chc_expr_children(expr: &ay_chc::ChcExpr) -> &[Arc<ay_chc::ChcExpr>] {
    match expr {
        ay_chc::ChcExpr::Op(_, args)
        | ay_chc::ChcExpr::FuncApp(_, _, args)
        | ay_chc::ChcExpr::PredicateApp(_, _, args) => args.as_slice(),
        ay_chc::ChcExpr::ConstArray(_, inner) => std::slice::from_ref(inner),
        _ => &[],
    }
}

fn collect_bridge_widths(
    expr: &ay_chc::ChcExpr,
    widths: &mut BTreeSet<u32>,
    saw_bridge: &mut bool,
) {
    if let ay_chc::ChcExpr::Op(op, _) = expr {
        match op {
            ay_chc::ChcOp::Int2Bv(width) => {
                widths.insert(*width);
                *saw_bridge = true;
            }
            ay_chc::ChcOp::Bv2Nat => *saw_bridge = true,
            _ => {}
        }
    }
    for child in chc_expr_children(expr) {
        collect_bridge_widths(child, widths, saw_bridge);
    }
}

fn collect_var_sorts(
    expr: &ay_chc::ChcExpr,
    out: &mut BTreeMap<String, BTreeSet<ay_chc::ChcSort>>,
) {
    if let ay_chc::ChcExpr::Var(var) = expr {
        out.entry(var.name.clone()).or_default().insert(var.sort.clone());
    }
    for child in chc_expr_children(expr) {
        collect_var_sorts(child, out);
    }
}

/// Record a top-level `(Int var) op (Int literal)` fact (either operand
/// order) into the per-variable `(lo, hi)` window bounds.
fn record_conjunct_bound(
    conjunct: &ay_chc::ChcExpr,
    bounds: &mut BTreeMap<String, (Option<i128>, Option<i128>)>,
) {
    let ay_chc::ChcExpr::Op(op, args) = conjunct else {
        return;
    };
    if !matches!(
        op,
        ay_chc::ChcOp::Lt
            | ay_chc::ChcOp::Le
            | ay_chc::ChcOp::Gt
            | ay_chc::ChcOp::Ge
            | ay_chc::ChcOp::Eq
    ) || args.len() != 2
    {
        return;
    }
    // (var, literal, var_first)
    let (var, literal, var_first) = match (args[0].as_ref(), args[1].as_ref()) {
        (ay_chc::ChcExpr::Var(var), ay_chc::ChcExpr::Int(literal))
            if var.sort == ay_chc::ChcSort::Int =>
        {
            (var, *literal, true)
        }
        (ay_chc::ChcExpr::Int(literal), ay_chc::ChcExpr::Var(var))
            if var.sort == ay_chc::ChcSort::Int =>
        {
            (var, *literal, false)
        }
        _ => return,
    };
    // Normalized fact about `var`: derived lower bound and/or upper bound.
    let (lo, hi) = match (op, var_first) {
        (ay_chc::ChcOp::Eq, _) => (Some(literal), Some(literal)),
        // var < c  ⇒ var <= c-1 ; c < var ⇒ var >= c+1 ; etc.
        (ay_chc::ChcOp::Lt, true) => (None, literal.checked_sub(1)),
        (ay_chc::ChcOp::Lt, false) => (literal.checked_add(1), None),
        (ay_chc::ChcOp::Le, true) => (None, Some(literal)),
        (ay_chc::ChcOp::Le, false) => (Some(literal), None),
        (ay_chc::ChcOp::Gt, true) => (literal.checked_add(1), None),
        (ay_chc::ChcOp::Gt, false) => (None, literal.checked_sub(1)),
        (ay_chc::ChcOp::Ge, true) => (Some(literal), None),
        (ay_chc::ChcOp::Ge, false) => (None, Some(literal)),
        _ => (None, None),
    };
    let entry = bounds.entry(var.name.clone()).or_insert((None, None));
    if let Some(lo) = lo {
        entry.0 = Some(entry.0.map_or(lo, |existing| existing.max(lo)));
    }
    if let Some(hi) = hi {
        entry.1 = Some(entry.1.map_or(hi, |existing| existing.min(hi)));
    }
}

/// Matched pieces of the R5 signed bv2nat-decode Ite, with original operand
/// orders retained so the rebuild preserves the source shape.
struct SignedDecodeParts<'a> {
    /// The decoded BV(w) term `W` (shared by the condition and both branches).
    bv_term: &'a Arc<ay_chc::ChcExpr>,
    /// Name of the Int variable the decode defines.
    var_name: &'a str,
    /// Whether the `#b1` literal is the first `Eq` operand in the condition.
    cond_literal_first: bool,
    /// Whether the Int var is the first `Eq` operand in the then-branch.
    then_var_first: bool,
    /// Whether the Int var is the first `Eq` operand in the else-branch.
    else_var_first: bool,
}

/// Match a sign-bit test `Eq(BvExtract(w-1,w-1)(W), #b1)` (either operand
/// order), returning the tested BV(w) term `W` and whether the `#b1` literal
/// came first. `W`'s sort is checked so a mis-width extract cannot match.
fn match_sign_bit_test<'a>(
    cond: &'a Arc<ay_chc::ChcExpr>,
    width: u32,
) -> Option<(&'a Arc<ay_chc::ChcExpr>, bool)> {
    let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Eq, cond_args) = cond.as_ref() else {
        return None;
    };
    let [cond_a, cond_b] = cond_args.as_slice() else {
        return None;
    };
    let sign_extract = |candidate: &'a Arc<ay_chc::ChcExpr>| -> Option<&'a Arc<ay_chc::ChcExpr>> {
        let ay_chc::ChcExpr::Op(ay_chc::ChcOp::BvExtract(high, low), extract_args) =
            candidate.as_ref()
        else {
            return None;
        };
        let [term] = extract_args.as_slice() else {
            return None;
        };
        (*high == width - 1 && *low == width - 1).then_some(term)
    };
    let one_bit = ay_chc::ChcExpr::BitVec(1, 1);
    let (bv_term, literal_first) = if *cond_a.as_ref() == one_bit {
        (sign_extract(cond_b)?, true)
    } else if *cond_b.as_ref() == one_bit {
        (sign_extract(cond_a)?, false)
    } else {
        return None;
    };
    (bv_term.sort() == ay_chc::ChcSort::BitVec(width)).then_some((bv_term, literal_first))
}

/// `candidate` is exactly `Bv2Nat(bv_term)` (the unsigned decode of `W`).
fn is_bv2nat_of(candidate: &Arc<ay_chc::ChcExpr>, bv_term: &Arc<ay_chc::ChcExpr>) -> bool {
    if let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Bv2Nat, bv2nat_args) = candidate.as_ref() {
        if let [inner] = bv2nat_args.as_slice() {
            return inner == bv_term;
        }
    }
    false
}

/// `candidate` is exactly `Sub(Bv2Nat(bv_term), 2^width)` — the wrap-corrected
/// decode branch. The subtrahend must be the EXACT `2^w` constant.
fn is_decode_minus_wrap(
    candidate: &Arc<ay_chc::ChcExpr>,
    bv_term: &Arc<ay_chc::ChcExpr>,
    width: u32,
) -> bool {
    if let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Sub, sub_args) = candidate.as_ref() {
        if let [minuend, subtrahend] = sub_args.as_slice() {
            return is_bv2nat_of(minuend, bv_term)
                && *subtrahend.as_ref() == ay_chc::ChcExpr::Int(1i128 << width);
        }
    }
    false
}

/// An Int-sorted `Var`'s name.
fn int_var_name(candidate: &Arc<ay_chc::ChcExpr>) -> Option<&str> {
    if let ay_chc::ChcExpr::Var(var) = candidate.as_ref() {
        (var.sort == ay_chc::ChcSort::Int).then_some(var.name.as_str())
    } else {
        None
    }
}

/// Match the R5t signed-decode TERM at `width` — the exact image of
/// `ay_bindings::Expr::bv2int_signed`, which the production typed-CHC reader
/// (`trust-bmc`'s `bv_to_int` with `signed: true`) builds for every wrap-exact
/// signed conversion:
///
/// `Ite(Eq(BvExtract(w-1,w-1)(W), #b1), Sub(Bv2Nat(W), 2^w), Bv2Nat(W))`
///
/// This is an Int-sorted TERM (branches are Int terms, not equalities), so it
/// is the operand of a surrounding equality rather than a conjunct. Returns the
/// decoded BV(w) term `W`.
///
/// The branch ORDER is pinned to the producer's (`then` = wrap-corrected under
/// the sign-set guard, `else` = plain): the complement form is deliberately NOT
/// matched, so no shape outside the exact producer image is ever rewritten.
fn match_signed_decode_term(expr: &ay_chc::ChcExpr, width: u32) -> Option<&Arc<ay_chc::ChcExpr>> {
    let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Ite, args) = expr else {
        return None;
    };
    let [cond, then_branch, else_branch] = args.as_slice() else {
        return None;
    };
    let (bv_term, _) = match_sign_bit_test(cond, width)?;
    (is_decode_minus_wrap(then_branch, bv_term, width) && is_bv2nat_of(else_branch, bv_term))
        .then_some(bv_term)
}

/// The Int variable a top-level conjunct pins to a signed-decode TERM, i.e.
/// `Eq(v, <R5t decode>)` in either operand order. Such a `v` satisfies R1(b):
/// `v = sbv(W)` lies in the signed window by construction.
fn signed_decode_definition_var(conjunct: &ay_chc::ChcExpr, width: u32) -> Option<&str> {
    let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Eq, args) = conjunct else {
        return None;
    };
    let [lhs, rhs] = args.as_slice() else {
        return None;
    };
    if match_signed_decode_term(rhs.as_ref(), width).is_some() {
        return int_var_name(lhs);
    }
    if match_signed_decode_term(lhs.as_ref(), width).is_some() {
        return int_var_name(rhs);
    }
    None
}

/// Match the exact R5 decode shape at `width`:
/// `Ite(Eq(#b1, BvExtract(w-1,w-1)(W)), Eq(Sub(Bv2Nat(W), 2^w), v), Eq(Bv2Nat(W), v))`
/// (each `Eq` in either operand order; `Sub` only as `bv2nat - 2^w`).
///
/// This is the BOOL-level form — the decode Ite lifted out of its defining
/// equality, which is what ay's clause normalizer produces downstream. The
/// pre-normalization producer image is the TERM form (`match_signed_decode_term`).
fn match_signed_decode<'a>(expr: &'a ay_chc::ChcExpr, width: u32) -> Option<SignedDecodeParts<'a>> {
    let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Ite, args) = expr else {
        return None;
    };
    let [cond, then_branch, else_branch] = args.as_slice() else {
        return None;
    };

    // Condition: sign-bit test of W.
    let (bv_term, cond_literal_first) = match_sign_bit_test(cond, width)?;

    // Branches: `v = bv2nat(W) - 2^w` (sign set) and `v = bv2nat(W)` (clear).
    let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Eq, then_args) = then_branch.as_ref() else {
        return None;
    };
    let [then_a, then_b] = then_args.as_slice() else {
        return None;
    };
    let (var_name, then_var_first) = if is_decode_minus_wrap(then_b, bv_term, width) {
        (int_var_name(then_a)?, true)
    } else if is_decode_minus_wrap(then_a, bv_term, width) {
        (int_var_name(then_b)?, false)
    } else {
        return None;
    };

    let ay_chc::ChcExpr::Op(ay_chc::ChcOp::Eq, else_args) = else_branch.as_ref() else {
        return None;
    };
    let [else_a, else_b] = else_args.as_slice() else {
        return None;
    };
    let (else_var, else_var_first) = if is_bv2nat_of(else_b, bv_term) {
        (int_var_name(else_a)?, true)
    } else if is_bv2nat_of(else_a, bv_term) {
        (int_var_name(else_b)?, false)
    } else {
        return None;
    };
    if else_var != var_name {
        return None;
    }

    Some(SignedDecodeParts {
        bv_term,
        var_name,
        cond_literal_first,
        then_var_first,
        else_var_first,
    })
}

/// Fragment translator for one clause constraint (rules R1-R7). Memoized by
/// node identity like `lower_expr`, so shared-`Arc` DAGs rewrite in O(nodes)
/// instead of O(paths).
struct BridgeRewriter<'a> {
    width: u32,
    window_min: i128,
    window_max: i128,
    admissible: &'a BTreeSet<String>,
    memo: RefCell<HashMap<*const ay_chc::ChcExpr, ay_chc::ChcExpr>>,
}

impl BridgeRewriter<'_> {
    /// Two's-complement pattern of `value` at the rewrite width (`mod 2^w`).
    fn pattern_literal(&self, value: i128) -> ay_chc::ChcExpr {
        let modulus = 1i128 << self.width; // width <= 126, fits i128
        ay_chc::ChcExpr::BitVec(value.rem_euclid(modulus) as u128, self.width)
    }

    /// The BitVec(w) image of an admissible Int variable (same name).
    fn image_var(&self, name: &str) -> ay_chc::ChcExpr {
        ay_chc::ChcExpr::var(ay_chc::ChcVar::new(name, ay_chc::ChcSort::BitVec(self.width)))
    }

    fn rewrite_arc(&self, expr: &Arc<ay_chc::ChcExpr>) -> Option<ay_chc::ChcExpr> {
        let key: *const ay_chc::ChcExpr = Arc::as_ptr(expr);
        if let Some(hit) = self.memo.borrow().get(&key) {
            return Some(hit.clone());
        }
        let rewritten = self.rewrite_node(expr.as_ref())?;
        self.memo.borrow_mut().insert(key, rewritten.clone());
        Some(rewritten)
    }

    fn rewrite_args(&self, args: &[Arc<ay_chc::ChcExpr>]) -> Option<Vec<Arc<ay_chc::ChcExpr>>> {
        args.iter().map(|arg| self.rewrite_arc(arg).map(Arc::new)).collect()
    }

    fn rewrite_node(&self, expr: &ay_chc::ChcExpr) -> Option<ay_chc::ChcExpr> {
        use ay_chc::{ChcExpr, ChcOp, ChcSort};
        match expr {
            // Bool and BV leaves pass through unchanged.
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => Some(expr.clone()),
            // R2: window-checked constant image.
            ChcExpr::Int(value) => (self.window_min <= *value && *value <= self.window_max)
                .then(|| self.pattern_literal(*value)),
            ChcExpr::Var(var) => match &var.sort {
                // G3 guarantees no admissible name occurs Bool/BV-sorted.
                ChcSort::Bool | ChcSort::BitVec(_) => Some(expr.clone()),
                // R1: admissible Int var -> same-name BV(w) image (G2 else).
                ChcSort::Int if self.admissible.contains(&var.name) => {
                    Some(self.image_var(&var.name))
                }
                _ => None,
            },
            ChcExpr::Op(op, args) => match op {
                // R5 first; a decode over a non-admissible var (or any other
                // Ite whose branches touch Bv2Nat/Sub) fails in the generic
                // recursion below — fail closed, never partially rewritten.
                ChcOp::Ite => {
                    if let Some(parts) = match_signed_decode(expr, self.width) {
                        if self.admissible.contains(parts.var_name) {
                            return self.rewrite_signed_decode(&parts);
                        }
                    }
                    // R5t: the Int-sorted signed-decode TERM collapses to its
                    // own decoded BV term. EXACT and unconditional (no
                    // admissibility needed): the term's value IS sbv(W) by the
                    // two's-complement definition, so it satisfies the
                    // rewriter's Int-term invariant `sbv(image) = term` with
                    // image = W, and its value always lies in the window.
                    if let Some(bv_term) = match_signed_decode_term(expr, self.width) {
                        return self.rewrite_arc(bv_term);
                    }
                    if args.len() != 3 {
                        return None;
                    }
                    Some(ChcExpr::Op(ChcOp::Ite, self.rewrite_args(args)?))
                }
                // R7: truth-functional structure, children rewritten in place.
                ChcOp::Not | ChcOp::And | ChcOp::Or | ChcOp::Implies | ChcOp::Iff => {
                    if args.is_empty() {
                        return None;
                    }
                    Some(ChcExpr::Op(*op, self.rewrite_args(args)?))
                }
                // R3 (Eq/Ne): operand sorts must agree and be in-fragment;
                // the operator is sort-generic, children carry the imaging.
                ChcOp::Eq | ChcOp::Ne => {
                    let [lhs, rhs] = args.as_slice() else {
                        return None;
                    };
                    let (lhs_sort, rhs_sort) = (lhs.sort(), rhs.sort());
                    if lhs_sort != rhs_sort
                        || !matches!(lhs_sort, ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(_))
                    {
                        return None;
                    }
                    Some(ChcExpr::Op(*op, self.rewrite_args(args)?))
                }
                // R3: signed comparisons for Int operands.
                ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => {
                    let [lhs, rhs] = args.as_slice() else {
                        return None;
                    };
                    if lhs.sort() != ChcSort::Int || rhs.sort() != ChcSort::Int {
                        return None;
                    }
                    let signed = match op {
                        ChcOp::Lt => ChcOp::BvSLt,
                        ChcOp::Le => ChcOp::BvSLe,
                        ChcOp::Gt => ChcOp::BvSGt,
                        ChcOp::Ge => ChcOp::BvSGe,
                        _ => unreachable!("guarded by the outer match arm"),
                    };
                    Some(ChcExpr::Op(signed, self.rewrite_args(args)?))
                }
                // Existing BV comparisons: already QF_BV, recurse for bridges.
                ChcOp::BvULt
                | ChcOp::BvULe
                | ChcOp::BvUGt
                | ChcOp::BvUGe
                | ChcOp::BvSLt
                | ChcOp::BvSLe
                | ChcOp::BvSGt
                | ChcOp::BvSGe => {
                    if args.len() != 2 {
                        return None;
                    }
                    Some(ChcExpr::Op(*op, self.rewrite_args(args)?))
                }
                // R4: bridge collapse at the single rewrite width.
                ChcOp::Int2Bv(bridge_width) => {
                    if *bridge_width != self.width {
                        return None;
                    }
                    let [inner] = args.as_slice() else {
                        return None;
                    };
                    match inner.as_ref() {
                        // int2bv_w(c) = c mod 2^w exactly, for ANY integer c.
                        ChcExpr::Int(value) => Some(self.pattern_literal(*value)),
                        ChcExpr::Var(var)
                            if var.sort == ChcSort::Int && self.admissible.contains(&var.name) =>
                        {
                            Some(self.image_var(&var.name))
                        }
                        _ => None,
                    }
                }
                // A Bv2Nat outside the matched R5 shape has no exact image.
                ChcOp::Bv2Nat => None,
                // Pure BV value operators: kept, children rewritten (R4).
                ChcOp::BvAdd
                | ChcOp::BvSub
                | ChcOp::BvMul
                | ChcOp::BvUDiv
                | ChcOp::BvURem
                | ChcOp::BvSDiv
                | ChcOp::BvSRem
                | ChcOp::BvSMod
                | ChcOp::BvAnd
                | ChcOp::BvOr
                | ChcOp::BvXor
                | ChcOp::BvNand
                | ChcOp::BvNor
                | ChcOp::BvXnor
                | ChcOp::BvNot
                | ChcOp::BvNeg
                | ChcOp::BvShl
                | ChcOp::BvLShr
                | ChcOp::BvAShr
                | ChcOp::BvComp
                | ChcOp::BvConcat
                | ChcOp::BvExtract(_, _)
                | ChcOp::BvZeroExtend(_)
                | ChcOp::BvSignExtend(_)
                | ChcOp::BvRotateLeft(_)
                | ChcOp::BvRotateRight(_)
                | ChcOp::BvRepeat(_) => {
                    if args.is_empty() {
                        return None;
                    }
                    Some(ChcExpr::Op(*op, self.rewrite_args(args)?))
                }
                // Int arithmetic outside the matched decode, arrays, and
                // anything else: outside the proven fragment (G4).
                _ => None,
            },
            // Reals, uninterpreted/constructor applications, arrays, markers:
            // outside the proven fragment (G4).
            _ => None,
        }
    }

    /// R5 rebuild: same Ite/BvExtract skeleton and operand orders, with the
    /// decode side of each branch replaced by the rewritten `W` and the Int
    /// var replaced by its BV(w) image.
    fn rewrite_signed_decode(&self, parts: &SignedDecodeParts<'_>) -> Option<ay_chc::ChcExpr> {
        use ay_chc::{ChcExpr, ChcOp};
        let bv_term = self.rewrite_arc(parts.bv_term)?;
        let image = self.image_var(parts.var_name);
        let sign_bit = ChcExpr::Op(
            ChcOp::BvExtract(self.width - 1, self.width - 1),
            vec![Arc::new(bv_term.clone())],
        );
        let one_bit = ChcExpr::BitVec(1, 1);
        let cond = if parts.cond_literal_first {
            op2(ChcOp::Eq, one_bit, sign_bit)
        } else {
            op2(ChcOp::Eq, sign_bit, one_bit)
        };
        let branch = |var_first: bool| {
            if var_first {
                op2(ChcOp::Eq, image.clone(), bv_term.clone())
            } else {
                op2(ChcOp::Eq, bv_term.clone(), image.clone())
            }
        };
        Some(ChcExpr::Op(
            ChcOp::Ite,
            vec![
                Arc::new(cond),
                Arc::new(branch(parts.then_var_first)),
                Arc::new(branch(parts.else_var_first)),
            ],
        ))
    }
}

// ===== Bit-vector overflow-predicate expansions (Trust Gap 3, build #29) =====
// ay-chc has no native overflow op, so each `BvXxxNoOverflow` predicate is
// expanded into its EXACT two's-complement definition (TRUE iff no overflow).
// All are standard equisatisfiable encodings — never false-PROVE / false-FAIL.

/// Width of a bitvector-sorted operand (overflow predicates apply only to
/// bitvectors; widths above 128 are out of range and stay fail-closed).
fn require_bv_width(operand: &Expr) -> NativeSolveResult<u32> {
    match operand.sort().inner() {
        SortInner::BitVec(bitvec) if bitvec.width <= 128 => Ok(bitvec.width),
        _ => Err(invalid_vc(format!(
            "overflow predicate operand is not a <=128-bit bitvector: {:?}",
            operand.sort()
        ))),
    }
}

/// All-ones value for a width-`w` bitvector (two's-complement `-1` / unsigned max).
fn bv_all_ones(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// Signed minimum (sign bit set) for a width-`w` bitvector.
fn bv_signed_min(width: u32) -> u128 {
    1u128 << (width - 1)
}

/// `BvSdivNoOverflow`: signed division overflows iff `a == INT_MIN && b == -1`.
fn lower_no_overflow_sdiv(lhs: &Expr, rhs: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    let width = require_bv_width(lhs)?;
    let a_is_min = op2(
        ay_chc::ChcOp::Eq,
        lower_expr(lhs)?,
        ay_chc::ChcExpr::BitVec(bv_signed_min(width), width),
    );
    let b_is_neg_one = op2(
        ay_chc::ChcOp::Eq,
        lower_expr(rhs)?,
        ay_chc::ChcExpr::BitVec(bv_all_ones(width), width),
    );
    Ok(ay_chc::ChcExpr::not(ay_chc::ChcExpr::and_vec(vec![a_is_min, b_is_neg_one])))
}

/// `BvNegNoOverflow`: signed negation overflows iff `a == INT_MIN`.
fn lower_no_overflow_neg(inner: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    let width = require_bv_width(inner)?;
    Ok(op2(
        ay_chc::ChcOp::Ne,
        lower_expr(inner)?,
        ay_chc::ChcExpr::BitVec(bv_signed_min(width), width),
    ))
}

/// `BvSubNoUnderflowUnsigned`: unsigned subtraction underflows iff `b > a`; safe
/// iff `b <= a`.
fn lower_no_underflow_sub_unsigned(lhs: &Expr, rhs: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    Ok(op2(ay_chc::ChcOp::BvULe, lower_expr(rhs)?, lower_expr(lhs)?))
}

/// `BvAddNoOverflowUnsigned`: safe iff `a + b <= MAX` iff `b <= ~a` (since
/// `~a == MAX - a`).
fn lower_no_overflow_add_unsigned(lhs: &Expr, rhs: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    let not_a = op1(ay_chc::ChcOp::BvNot, lower_expr(lhs)?);
    Ok(op2(ay_chc::ChcOp::BvULe, lower_expr(rhs)?, not_a))
}

/// `BvAdd/BvSubNoOverflowSigned`: sign-extend both by one bit, operate in `w+1`
/// bits, and require the top two bits of the result to be equal (no signed
/// overflow).
fn lower_no_overflow_addsub_signed(
    op: ay_chc::ChcOp,
    lhs: &Expr,
    rhs: &Expr,
) -> NativeSolveResult<ay_chc::ChcExpr> {
    let width = require_bv_width(lhs)?;
    let a = op1(ay_chc::ChcOp::BvSignExtend(1), lower_expr(lhs)?);
    let b = op1(ay_chc::ChcOp::BvSignExtend(1), lower_expr(rhs)?);
    let result = op2(op, a, b);
    let top = op1(ay_chc::ChcOp::BvExtract(width, width), result.clone());
    let next = op1(ay_chc::ChcOp::BvExtract(width - 1, width - 1), result);
    Ok(op2(ay_chc::ChcOp::Eq, top, next))
}

/// `BvMulNoOverflowUnsigned`: zero-extend to `2w`, multiply, require the high `w`
/// bits to be zero.
fn lower_no_overflow_mul_unsigned(lhs: &Expr, rhs: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    let width = require_bv_width(lhs)?;
    let a = op1(ay_chc::ChcOp::BvZeroExtend(width), lower_expr(lhs)?);
    let b = op1(ay_chc::ChcOp::BvZeroExtend(width), lower_expr(rhs)?);
    let product = op2(ay_chc::ChcOp::BvMul, a, b);
    let high = op1(ay_chc::ChcOp::BvExtract(2 * width - 1, width), product);
    Ok(op2(ay_chc::ChcOp::Eq, high, ay_chc::ChcExpr::BitVec(0, width)))
}

/// `BvMulNoOverflowSigned`: sign-extend to `2w`, multiply, require the `2w`
/// product to equal the sign-extension of its low `w` bits.
fn lower_no_overflow_mul_signed(lhs: &Expr, rhs: &Expr) -> NativeSolveResult<ay_chc::ChcExpr> {
    let width = require_bv_width(lhs)?;
    let a = op1(ay_chc::ChcOp::BvSignExtend(width), lower_expr(lhs)?);
    let b = op1(ay_chc::ChcOp::BvSignExtend(width), lower_expr(rhs)?);
    let product = op2(ay_chc::ChcOp::BvMul, a, b);
    let low = op1(ay_chc::ChcOp::BvExtract(width - 1, 0), product.clone());
    let low_sign_extended = op1(ay_chc::ChcOp::BvSignExtend(width), low);
    Ok(op2(ay_chc::ChcOp::Eq, product, low_sign_extended))
}

/// Lower an integer constant through ay's i128-wide `ChcExpr::Int` boundary.
/// Constants beyond i128 fail closed.
fn lower_int_constant(value: &impl Display) -> NativeSolveResult<ay_chc::ChcExpr> {
    let text = value.to_string();
    if let Ok(v) = text.parse::<i64>() {
        return Ok(ay_chc::ChcExpr::Int(i128::from(v)));
    }
    let wide = text
        .parse::<i128>()
        .map_err(|_| invalid_vc(format!("integer constant `{text}` does not fit i128")))?;
    // i128-lockstep (ay rank 6 Phase 1): `ChcExpr::Int` is now i128-wide, so an
    // i128-range constant lowers as a PLAIN constant. Beyond-i128 constants
    // still fail closed at the parse above.
    Ok(ay_chc::ChcExpr::Int(wide))
}

fn parse_i64(value: &impl Display, role: &str) -> NativeSolveResult<i64> {
    value
        .to_string()
        .parse::<i64>()
        .map_err(|_| invalid_vc(format!("{role} `{value}` does not fit native ay-chc i64")))
}

fn parse_u128(value: &impl Display, role: &str) -> NativeSolveResult<u128> {
    value
        .to_string()
        .parse::<u128>()
        .map_err(|_| invalid_vc(format!("{role} `{value}` does not fit native ay-chc u128")))
}

fn unsupported_sort(sort: &Sort) -> NativeSolveError {
    invalid_vc(format!("unsupported sort for native typed ay-chc lowering: {sort:?}"))
}

fn unsupported_expr(expr: &ExprValue) -> NativeSolveError {
    invalid_vc(format!("unsupported expression for native typed ay-chc lowering: {expr:?}"))
}

fn invalid_vc(detail: impl Into<String>) -> NativeSolveError {
    NativeSolveError::InvalidInput {
        field: String::from("request.obligation.vc"),
        detail: detail.into(),
    }
}

#[cfg(test)]
mod memoization_tests {
    //! Regression guard for the exponential `lower_expr` blow-up. An
    //! `ay_bindings::Expr` is a shared `Arc<ExprValue>` DAG, so a self-doubling value
    //! (`e = e + e`, N deep) has only `O(N)` distinct nodes but `O(2^N)` root-to-leaf
    //! paths. Without identity memoization the structural lowering re-expands every
    //! shared subterm once per path — `O(2^N)` `ChcExpr` nodes — which exhausts memory
    //! (an OOM that can take the machine down). The identity cache in `lower_expr`
    //! keeps it `O(N)`.
    //!
    //! NOTE: parse-verified only; not executed in-session — the pinned
    //! `nightly-2025-12-03` toolchain ICEs compiling `serde_derive v1.0.228`, which
    //! blocks every build of this crate. Re-run once that blocker is cleared.
    use super::*;
    use ay_bindings::{Expr, Sort};
    use std::collections::HashSet;

    /// Distinct `ChcExpr` allocations reachable from `expr`, counted by `Arc` identity
    /// so a shared-DAG node is counted exactly once.
    fn distinct_nodes(expr: &ay_chc::ChcExpr, seen: &mut HashSet<*const ay_chc::ChcExpr>) -> usize {
        let children: &[Arc<ay_chc::ChcExpr>] = match expr {
            ay_chc::ChcExpr::Op(_, args)
            | ay_chc::ChcExpr::FuncApp(_, _, args)
            | ay_chc::ChcExpr::PredicateApp(_, _, args) => args.as_slice(),
            ay_chc::ChcExpr::ConstArray(_, inner) => std::slice::from_ref(inner),
            _ => &[],
        };
        let mut total = 1;
        for child in children {
            if seen.insert(Arc::as_ptr(child)) {
                total += distinct_nodes(child, seen);
            }
        }
        total
    }

    /// `e = e + e` repeated 18 times: an 18-node shared `Arc<ExprValue>` DAG with `2^18`
    /// root-to-leaf paths. Memoized lowering stays linear (a few dozen `ChcExpr` nodes);
    /// the pre-fix structural lowering would materialize ~`2^19` distinct nodes. The
    /// depth is kept modest so a regression fails this assertion *without* OOM-ing the
    /// test runner.
    #[test]
    fn self_doubling_expr_lowers_to_linear_node_count() {
        let mut expr = Expr::var("v", Sort::bitvec(64));
        for _ in 0..18 {
            expr = expr.clone().bvadd(expr);
        }

        let lowered = lower_expr(&expr).expect("self-doubling bitvector expr must lower");

        let mut seen = HashSet::new();
        let nodes = distinct_nodes(&lowered, &mut seen);
        assert!(
            nodes < 1000,
            "memoized lowering of an 18-deep self-doubling DAG must stay linear; got \
             {nodes} distinct ChcExpr nodes (un-memoized would be ~2^19)"
        );
    }
}

#[cfg(test)]
mod large_int_lowering_tests {
    //! Integer constants past i64 lower directly through ay's i128-wide
    //! `ChcExpr::Int` instead of failing the whole obligation to Unsupported.
    use super::*;

    /// Evaluate an integer expression exactly with i128 arithmetic.
    fn eval(expr: &ay_chc::ChcExpr) -> i128 {
        match expr {
            ay_chc::ChcExpr::Int(v) => *v,
            ay_chc::ChcExpr::Op(op, args) => {
                let mut vals = args.iter().map(|a| eval(a));
                match op {
                    ay_chc::ChcOp::Add => vals.sum(),
                    ay_chc::ChcOp::Mul => vals.product(),
                    ay_chc::ChcOp::Neg => -vals.next().expect("neg has one arg"),
                    ay_chc::ChcOp::Sub => {
                        let first = vals.next().expect("sub has args");
                        first - vals.sum::<i128>()
                    }
                    other => panic!("unexpected op in literal tree: {other:?}"),
                }
            }
            other => panic!("unexpected node in literal tree: {other:?}"),
        }
    }

    #[test]
    fn u64_max_lowers_to_exact_constant() {
        let expr = lower_int_constant(&"18446744073709551615").expect("u64::MAX must lower");
        assert_eq!(eval(&expr), 18_446_744_073_709_551_615_i128);
        assert!(
            matches!(expr, ay_chc::ChcExpr::Int(_)),
            "i128-wide ChcExpr::Int must carry u64::MAX as a PLAIN constant"
        );
    }

    #[test]
    fn i64_range_constants_stay_plain_int() {
        assert!(matches!(lower_int_constant(&"42"), Ok(ay_chc::ChcExpr::Int(42))));
        assert!(matches!(lower_int_constant(&"-5"), Ok(ay_chc::ChcExpr::Int(-5))));
        assert!(matches!(
            lower_int_constant(&i64::MAX.to_string()),
            Ok(ay_chc::ChcExpr::Int(x)) if x == i64::MAX as i128
        ));
    }

    #[test]
    fn negative_wide_constant_lowers_exactly() {
        let expr = lower_int_constant(&"-18446744073709551615").expect("negative wide must lower");
        assert_eq!(eval(&expr), -18_446_744_073_709_551_615_i128);
    }

    #[test]
    fn beyond_i128_fails_closed() {
        // 2^127 does not fit i128 (max is 2^127 - 1) — must be a lowering error,
        // never a silent wrap.
        assert!(lower_int_constant(&"170141183460469231731687303715884105728").is_err());
    }
}

#[cfg(test)]
mod bridge_elimination_tests {
    //! Receipt-lane P0b: production pins for the Int↔BV signed-bridge
    //! elimination. The positive case is the exact shape of the dumped
    //! `chc_abs.txt` request-2-proof-3 obligation (abs_like's `-x` branch
    //! postcondition row), which was UNDECIDED at a 60s direct-SMT budget
    //! before the rewrite and decides in milliseconds after it. Every
    //! fail-closed gate (missing window, mixed widths, name capture) must
    //! leave the lowered clause constraint structurally identical to the
    //! plain per-conjunct lowering.
    use std::time::Duration;

    use ay_bindings::{Expr, Sort};

    use super::*;

    const I32_MIN: i128 = -2_147_483_648;
    const I32_MAX: i128 = 2_147_483_647;

    fn obligation_from_conjuncts(conjuncts: Vec<Expr>) -> trust_mc_core::MirChcPdrObligation {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("error");
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::new(None, conjuncts),
            trust_mc_core::RelationApp::nullary("error"),
        ));
        trust_mc_core::MirChcPdrObligation::new(
            "bridge-elim-test",
            "crate::bridge_elim",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        )
    }

    fn lowered_problem(conjuncts: Vec<Expr>) -> ay_chc::ChcProblem {
        lower_obligation(&obligation_from_conjuncts(conjuncts)).expect("bridge fixture must lower")
    }

    fn lowered_constraint(conjuncts: Vec<Expr>) -> ay_chc::ChcExpr {
        lowered_problem(conjuncts).clauses()[0]
            .body
            .constraint
            .clone()
            .expect("lowered clause carries a constraint")
    }

    /// What `lower_rule_body` builds BEFORE `eliminate_signed_int_bridges`
    /// runs: per-conjunct `lower_expr` + `and_vec`. Equality against this is
    /// the "left byte-identical" assertion for the fail-closed gates.
    fn unrewritten_constraint(conjuncts: &[Expr]) -> ay_chc::ChcExpr {
        ay_chc::ChcExpr::and_vec(
            conjuncts
                .iter()
                .map(|conjunct| lower_expr(conjunct).expect("conjunct must lower"))
                .collect(),
        )
    }

    /// True when any Int-theory or bridge residue survives (the rewrite must
    /// leave NONE of these behind).
    fn mentions_int_or_bridge(expr: &ay_chc::ChcExpr) -> bool {
        match expr {
            ay_chc::ChcExpr::Int(_) => true,
            ay_chc::ChcExpr::Var(var) => var.sort == ay_chc::ChcSort::Int,
            ay_chc::ChcExpr::Op(
                ay_chc::ChcOp::Int2Bv(_)
                | ay_chc::ChcOp::Bv2Nat
                | ay_chc::ChcOp::Add
                | ay_chc::ChcOp::Sub
                | ay_chc::ChcOp::Mul
                | ay_chc::ChcOp::Div
                | ay_chc::ChcOp::Mod
                | ay_chc::ChcOp::Neg
                | ay_chc::ChcOp::Lt
                | ay_chc::ChcOp::Le
                | ay_chc::ChcOp::Gt
                | ay_chc::ChcOp::Ge,
                _,
            ) => true,
            _ => chc_expr_children(expr).iter().any(|child| mentions_int_or_bridge(child)),
        }
    }

    fn strict_pdr_config() -> ay_encode::invoke::EncodeConfig {
        ay_encode::invoke::EncodeConfig::new()
            .with_engine(ay_encode::invoke::Engine::Pdr)
            .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
            .with_timeout(Duration::from_secs(30))
    }

    /// The `-x` branch postcondition row of `chc_abs.txt` request-2-proof-3,
    /// width-parameterized. At `width == 32` this is the exact dumped typed
    /// obligation: guard-definition equations, the signed window facts, the
    /// `W = 0 - int2bv(x)` sign-decode Ite defining the return value, and the
    /// negated `result >= 0` postcondition.
    fn abs_neg_branch_conjuncts(width: u32, min: i128, max: i128) -> Vec<Expr> {
        let x = || Expr::var("x", Sort::int());
        let r = || Expr::var("_0#s4_0", Sort::int());
        let b2 = || Expr::var("_2", Sort::bool());
        let b3 = || Expr::var("_3", Sort::bool());
        let b4 = || Expr::var("_4", Sort::bool());
        let min_lit = move || Expr::int(min);
        let max_lit = move || Expr::int(max);
        let zero = || Expr::int(0);
        let w_term = move || zero().int2bv(width).bvsub(x().int2bv(width));
        let wrap = 1i128 << width;
        vec![
            min_lit().eq(x()).eq(b2()),
            min_lit().eq(x()).eq(b2()),
            min_lit().eq(x()).eq(b4()),
            min_lit().eq(x()).eq(b4()),
            x().int_lt(zero()).eq(b3()),
            x().int_lt(zero()).eq(b3()),
            x().int_ge(min_lit()),
            Expr::ite(
                Expr::bitvec_const(1, 1).eq(w_term().extract(width - 1, width - 1)),
                w_term().bv2int().int_sub(Expr::int(wrap)).eq(r()),
                w_term().bv2int().eq(r()),
            ),
            x().int_le(max_lit()),
            x().int_lt(zero()),
            min_lit().eq(x()).not(),
            r().int_ge(zero()).not(),
            b4().not(),
        ]
    }

    fn abs_neg_branch_conjuncts_32() -> Vec<Expr> {
        abs_neg_branch_conjuncts(32, I32_MIN, I32_MAX)
    }

    fn bv64(value: u64) -> Expr {
        Expr::bitvec_const(value, 64)
    }

    fn bvvar64(name: &str) -> Expr {
        Expr::var(name, Sort::bitvec(64))
    }

    fn inc_xp1() -> Expr {
        bv64(1).bvadd(bvvar64("x"))
    }

    /// inc's postcondition row (`chc_inc.txt` request-1-proof-2): already
    /// pure QF_BV, must never be touched by the bridge elimination.
    fn inc_postcondition_conjuncts() -> Vec<Expr> {
        vec![
            bv64(0).bvule(inc_xp1()),
            bv64(0).bvule(bvvar64("x")),
            bv64(0).bvule(bvvar64("x")),
            inc_xp1().bvule(bv64(u64::MAX)),
            bvvar64("x").bvule(bv64(u64::MAX)),
            bvvar64("x").bvule(bv64(u64::MAX)),
            bvvar64("x").bvult(bv64(u64::MAX)),
            inc_xp1().eq(bvvar64("_2.0")),
            bvvar64("_0").eq(bvvar64("_2.0")),
            inc_xp1().eq(bvvar64("_0")).not(),
            bv64(u64::MAX).bvult(inc_xp1()).or(inc_xp1().eq(bvvar64("_0"))),
        ]
    }

    // (a) The exact chc_abs.txt request-2-proof-3 query rewrites to pure
    // QF_BV, is UNSAT under the direct-SMT budget, and PROVES through the
    // strict PDR entry the native runner uses.
    #[test]
    fn abs_neg_bridge_row_rewrites_to_pure_qf_bv_and_proves() {
        let conjuncts = abs_neg_branch_conjuncts_32();
        let problem = lowered_problem(conjuncts);
        let constraint = problem.clauses()[0].body.constraint.clone().expect("clause constraint");
        assert!(
            !mentions_int_or_bridge(&constraint),
            "bridge elimination must produce pure QF_BV, got: {constraint:?}"
        );

        let mut smt = ay_chc::SmtContext::new();
        smt.reset();
        let result = smt.check_sat_with_timeout(&constraint, Duration::from_secs(5));
        assert!(
            result.is_unsat(),
            "rewritten -x branch postcondition VC must be UNSAT, got {result:?}"
        );

        let verdict =
            ay_encode::invoke::solve(problem, &strict_pdr_config()).expect("PDR solve runs");
        assert!(
            matches!(verdict, ay_encode::verdict::AyVerdict::Proved { .. }),
            "expected Proved for the rewritten -x branch row, got {verdict:?}"
        );
    }

    // Width-generic: the same decode shape at width 64 (i64 semantics, wrap
    // correction 2^64 beyond i64::MAX) rewrites and proves identically.
    #[test]
    fn abs_neg_bridge_row_width64_rewrites_and_proves() {
        let min = -(1i128 << 63);
        let max = (1i128 << 63) - 1;
        let conjuncts = abs_neg_branch_conjuncts(64, min, max);
        let problem = lowered_problem(conjuncts);
        let constraint = problem.clauses()[0].body.constraint.clone().expect("clause constraint");
        assert!(
            !mentions_int_or_bridge(&constraint),
            "width-64 bridge elimination must produce pure QF_BV, got: {constraint:?}"
        );

        let mut smt = ay_chc::SmtContext::new();
        smt.reset();
        let result = smt.check_sat_with_timeout(&constraint, Duration::from_secs(5));
        assert!(result.is_unsat(), "width-64 rewritten VC must be UNSAT, got {result:?}");

        let verdict =
            ay_encode::invoke::solve(problem, &strict_pdr_config()).expect("PDR solve runs");
        assert!(
            matches!(verdict, ay_encode::verdict::AyVerdict::Proved { .. }),
            "expected Proved for the width-64 row, got {verdict:?}"
        );
    }

    // (b) An Int var without a full signed window (Ge/Le facts removed; the
    // remaining Lt(x, 0) gives only an upper bound) is NOT rewritten: the
    // clause constraint stays structurally identical to the plain lowering.
    #[test]
    fn unbounded_int_var_is_not_rewritten() {
        let mut conjuncts = abs_neg_branch_conjuncts_32();
        let upper = conjuncts.remove(8); // x <= i32::MAX
        let lower = conjuncts.remove(6); // x >= i32::MIN
        drop((upper, lower));
        let lowered = lowered_constraint(conjuncts.clone());
        assert_eq!(
            lowered,
            unrewritten_constraint(&conjuncts),
            "window-less Int var must leave the clause byte-identical"
        );
    }

    // (c) inc's pure-BV postcondition row has no bridge atoms: untouched.
    #[test]
    fn pure_bv_inc_row_is_untouched() {
        let conjuncts = inc_postcondition_conjuncts();
        let lowered = lowered_constraint(conjuncts.clone());
        assert_eq!(
            lowered,
            unrewritten_constraint(&conjuncts),
            "bridge-free pure-BV clause must lower unchanged"
        );
    }

    // Mixed Int2Bv widths in one clause fail closed (gate G1). The extra
    // 64-bit bridge conjunct is deliberately NOT a tautology: `add_clause`'s
    // pre-existing constant simplifier folds `Eq(t, t)` away on every path,
    // which would mask the comparison this test pins.
    #[test]
    fn mixed_bridge_widths_fail_closed() {
        let mut conjuncts = abs_neg_branch_conjuncts_32();
        conjuncts.push(
            Expr::var("x", Sort::int()).int2bv(64).eq(Expr::var("wide_probe", Sort::bitvec(64))),
        );
        let lowered = lowered_constraint(conjuncts.clone());
        assert_eq!(
            lowered,
            unrewritten_constraint(&conjuncts),
            "mixed bridge widths must leave the clause byte-identical"
        );
    }

    // A window-bounded Int var whose NAME also occurs as a BV var fails
    // closed (gate G3): re-sorting would merge two distinct variables.
    #[test]
    fn rewritten_name_colliding_with_bv_var_fails_closed() {
        let x_int = || Expr::var("x", Sort::int());
        let x_bv = || Expr::var("x", Sort::bitvec(32));
        let y_bv = || Expr::var("y", Sort::bitvec(32));
        let conjuncts = vec![
            x_int().int_ge(Expr::int(I32_MIN)),
            x_int().int_le(Expr::int(I32_MAX)),
            x_int().int2bv(32).eq(y_bv()),
            x_bv().eq(y_bv()),
        ];
        let lowered = lowered_constraint(conjuncts.clone());
        assert_eq!(
            lowered,
            unrewritten_constraint(&conjuncts),
            "Int/BV name collision must leave the clause byte-identical"
        );
    }

    // Falsification direction: a genuinely SAT bridge clause (postcondition
    // check un-negated, so the error IS derivable, e.g. x = -1 => W = 1 =>
    // result = 1 >= 0) must stay SAT after the rewrite and refute through
    // PDR — the rewrite preserves satisfiability in BOTH directions and can
    // never manufacture a proof.
    #[test]
    fn satisfiable_bridge_variant_still_refutes_after_rewrite() {
        let mut conjuncts = abs_neg_branch_conjuncts_32();
        conjuncts[11] = Expr::var("_0#s4_0", Sort::int()).int_ge(Expr::int(0));
        let problem = lowered_problem(conjuncts);
        let constraint = problem.clauses()[0].body.constraint.clone().expect("clause constraint");
        assert!(
            !mentions_int_or_bridge(&constraint),
            "the SAT variant is inside the fragment and must still rewrite"
        );

        let mut smt = ay_chc::SmtContext::new();
        smt.reset();
        let result = smt.check_sat_with_timeout(&constraint, Duration::from_secs(5));
        assert!(result.is_sat(), "un-negated variant must stay SAT, got {result:?}");

        // Production refutation lane for this acyclic shape: the direct-SMT
        // decision (run BEFORE PDR in `solve_typed_chc_pdr_full_with_ay`) must
        // compose a real error derivation from the rewritten problem.
        let decision = crate::direct_smt_cex::acyclic_direct_smt_decision(&problem);
        assert!(
            matches!(decision, crate::direct_smt_cex::AcyclicDecision::Unsafe(_)),
            "expected the acyclic direct-SMT decision to refute the derivable-error variant"
        );
    }
}

#[cfg(test)]
mod producer_shape_bridge_tests {
    //! Receipt-lane: pins for the PRODUCTION shape of
    //! `trust_ir-native-trust_mc-request-2-proof-3` (the wrap-exact signed-Neg
    //! postcondition row of `s1c_branch_abs_proves::abs_like`), reconstructed
    //! exactly as the compiler emits it:
    //!   * a deep LEFT-NESTED BINARY `And` tree (the payload builds `a.and(b)`
    //!     pairwise), so the signed window facts are NOT root-level conjuncts;
    //!   * the return value pinned by the PRIMITIVE `bv2int_signed` decode,
    //!     which is an Int-sorted TERM inside an equality — the pre-
    //!     normalization producer image, not the Bool-level Ite form.
    //! Before the R5t + And-flattening extension this row lowered unrewritten
    //! and ay returned Unknown (Inconclusive) on it.
    use std::time::Duration;

    use ay_bindings::{Expr, Sort};

    use super::*;

    const I32_MIN: i128 = -2_147_483_648;
    const I32_MAX: i128 = 2_147_483_647;

    /// The wrap-exact signed negation `sbv(0 -_32 x)`, built through the same
    /// `bv2int_signed` call the typed-CHC reader uses for `bv_to_int`/signed.
    fn signed_neg_decode() -> Expr {
        Expr::int(0).int2bv(32).bvsub(Expr::var("x", Sort::int()).int2bv(32)).bv2int_signed()
    }

    /// The exact production constraint tree. `postcondition_holds` selects the
    /// UNSAT direction (`¬(result >= 0)`, the real VC) or the SAT direction
    /// (`result >= 0`, whose error IS derivable) for the falsification pin.
    fn production_neg_row(negated_postcondition: bool) -> Expr {
        let x = || Expr::var("x", Sort::int());
        let r = || Expr::var("_0#s4_0", Sort::int());
        let b2 = || Expr::var("_2", Sort::bool());
        let b3 = || Expr::var("_3", Sort::bool());
        let b4 = || Expr::var("_4", Sort::bool());
        let min = || Expr::int(I32_MIN);
        let is_min = || x().eq(min());
        let is_neg = || x().int_lt(Expr::int(0));
        let post = if negated_postcondition {
            r().int_ge(Expr::int(0)).not()
        } else {
            r().int_ge(Expr::int(0))
        };
        let guards = Expr::bool_const(true)
            .and(b2().eq(is_min()))
            .and(b3().eq(is_neg()))
            .and(b4().eq(is_min()));
        let path = is_min()
            .not()
            .and(is_neg())
            .and(b4().not())
            // The signed window facts live HERE, three `And` levels down.
            .and(x().int_ge(min()).and(x().int_le(Expr::int(I32_MAX))));
        let body = b2()
            .eq(is_min())
            .and(b3().eq(is_neg()))
            .and(b4().eq(is_min()))
            .and(r().eq(signed_neg_decode()).and(post));
        guards.and(path.and(body))
    }

    fn lowered(constraint: Expr) -> ay_chc::ChcProblem {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("error");
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::new(None, vec![constraint]),
            trust_mc_core::RelationApp::nullary("error"),
        ));
        lower_obligation(&trust_mc_core::MirChcPdrObligation::new(
            "trust_ir-native-trust_mc-request-2-proof-3",
            "s1c_branch_abs_proves::abs_like",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        ))
        .expect("production row lowers")
    }

    fn constraint_of(problem: &ay_chc::ChcProblem) -> ay_chc::ChcExpr {
        problem.clauses()[0].body.constraint.clone().expect("clause constraint")
    }

    fn has_int_or_bridge(expr: &ay_chc::ChcExpr) -> bool {
        match expr {
            ay_chc::ChcExpr::Int(_) => true,
            ay_chc::ChcExpr::Var(var) => var.sort == ay_chc::ChcSort::Int,
            ay_chc::ChcExpr::Op(
                ay_chc::ChcOp::Int2Bv(_)
                | ay_chc::ChcOp::Bv2Nat
                | ay_chc::ChcOp::Sub
                | ay_chc::ChcOp::Lt
                | ay_chc::ChcOp::Le
                | ay_chc::ChcOp::Gt
                | ay_chc::ChcOp::Ge,
                _,
            ) => true,
            _ => chc_expr_children(expr).iter().any(|c| has_int_or_bridge(c)),
        }
    }

    /// The real VC direction: rewrites to pure QF_BV and is UNSAT (proved).
    #[test]
    fn production_neg_row_rewrites_and_is_unsat() {
        let problem = lowered(production_neg_row(true));
        let constraint = constraint_of(&problem);
        assert!(
            !has_int_or_bridge(&constraint),
            "production Neg row must rewrite to pure QF_BV, got: {constraint:?}"
        );

        let mut smt = ay_chc::SmtContext::new();
        smt.reset();
        let result = smt.check_sat_with_timeout(&constraint, Duration::from_secs(5));
        assert!(result.is_unsat(), "rewritten production Neg row must be UNSAT, got {result:?}");

        // The lane production actually uses for this acyclic shape.
        let decision = crate::direct_smt_cex::acyclic_direct_smt_decision(&problem);
        assert!(
            matches!(decision, crate::direct_smt_cex::AcyclicDecision::Safe),
            "acyclic direct-SMT must decide the rewritten production Neg row SAFE"
        );
    }

    /// FALSIFICATION PIN: the SAT direction must stay SAT after the rewrite and
    /// still refute. The rewrite is equisatisfiable in BOTH directions, so it
    /// can never manufacture a proof out of a derivable error.
    #[test]
    fn production_neg_row_sat_direction_still_refutes() {
        let problem = lowered(production_neg_row(false));
        let constraint = constraint_of(&problem);
        assert!(
            !has_int_or_bridge(&constraint),
            "the SAT direction is the same fragment and must also rewrite"
        );

        let mut smt = ay_chc::SmtContext::new();
        smt.reset();
        let result = smt.check_sat_with_timeout(&constraint, Duration::from_secs(5));
        assert!(result.is_sat(), "un-negated production row must stay SAT, got {result:?}");

        let decision = crate::direct_smt_cex::acyclic_direct_smt_decision(&problem);
        assert!(
            matches!(decision, crate::direct_smt_cex::AcyclicDecision::Unsafe(_)),
            "acyclic direct-SMT must refute the derivable-error direction"
        );
    }

    /// Gate pin (G2): with the signed window facts removed, `x` is no longer
    /// R1-admissible, so the whole clause must fail closed — the decode TERM
    /// pins `_0#s4_0` but must NOT license re-sorting `x`.
    ///
    /// NOTE the baseline: `lower_obligation` stores the clause through
    /// `add_clause`, whose own constant-folder flattens `And` trees and lifts
    /// `Ite`s out of equalities, so the stored constraint is NOT byte-equal to
    /// the raw `lower_expr` output even when nothing is rewritten. The gate is
    /// therefore asserted directly on the rewrite entry point, plus end-to-end
    /// by the surviving Int-theory residue.
    #[test]
    fn production_shape_without_window_facts_fails_closed() {
        let x = || Expr::var("x", Sort::int());
        let r = || Expr::var("_0#s4_0", Sort::int());
        let conjunct = x()
            .int_lt(Expr::int(0))
            .and(r().eq(signed_neg_decode()).and(r().int_ge(Expr::int(0)).not()));

        let raw = lower_expr(&conjunct).expect("conjunct lowers");
        assert!(
            rewrite_bridged_constraint(&raw, &[], &[]).is_none(),
            "window-less `x` must refuse the rewrite at the gate"
        );

        let constraint = constraint_of(&lowered(conjunct));
        assert!(
            has_int_or_bridge(&constraint),
            "a refused clause must keep its Int/bridge encoding, got: {constraint:?}"
        );
    }

    /// The And-flattening is what exposes those window facts: a scan that only
    /// looked at the root's children would see 2 conjuncts and miss them.
    #[test]
    fn nested_and_tree_is_flattened_for_fact_discovery() {
        let constraint = lower_expr(&production_neg_row(true)).expect("row lowers");
        let root_children = match &constraint {
            ay_chc::ChcExpr::Op(ay_chc::ChcOp::And, args) => args.len(),
            _ => 1,
        };
        let flattened = top_level_conjuncts(&constraint);
        assert_eq!(root_children, 2, "production payload is a BINARY And tree");
        assert!(
            flattened.len() > root_children,
            "flattening must expose more than the root's children"
        );
        let mut bounds: BTreeMap<String, (Option<i128>, Option<i128>)> = BTreeMap::new();
        for conjunct in &flattened {
            record_conjunct_bound(conjunct, &mut bounds);
        }
        let (lo, hi) = bounds.get("x").copied().expect("x must gain window bounds");
        assert!(lo.is_some() && hi.is_some(), "x must be window-bounded, got {lo:?}..{hi:?}");
    }
}
