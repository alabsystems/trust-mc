// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constructor-guard collection for CHC rule generation.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, SortInner};
use tracing::debug;

use crate::codegen_ay::types::CtorFieldExt;

/// Collect `((_ is Constructor) container)` guards for every DatatypeSelector
/// on a multi-constructor datatype found in `exprs`.
///
/// Z3 PDR requires these guards to treat accessor functions as interpreted
/// (Part of #3207). Without them, nested accessors like `(fld_val (value x))`
/// are treated as uninterpreted, causing UNKNOWN instead of PROOF/CTREX.
/// Structural identity for a selector's container.
///
/// The dedup key below uses POINTER identity, which cannot group two
/// structurally-equal `Var` nodes. Variant-conflict detection must, so a
/// variable is keyed by name.
fn container_identity(container: &Expr) -> String {
    match container.value() {
        ExprValue::Var { name } => format!("v:{name}"),
        other => format!("p:{:p}", std::ptr::from_ref(other)),
    }
}

/// Containers that carry selectors of MORE THAN ONE constructor in `exprs`.
///
/// A guard may only be asserted when the block's path already establishes the
/// container's constructor. When one container is read through both
/// `Ok_field_0` and `Err_field_0` — which is what `find().is_ok()` produces at
/// a merge point, where the value comes from `Ok(..)` on one predecessor and
/// `Err(..)` on another — the constructor is NOT established. The two possible
/// guards are mutually exclusive, so asserting EITHER is an arbitrary choice
/// that prunes the complementary path: observed as the only edge out of the
/// block becoming infeasible, every check unreachable, and the harness reported
/// VACUOUS.
///
/// Same rule `pinned_constructors` already applies to bindings ("a name bound
/// to two different constructors is dropped: that is not a pin"), and the same
/// trade: dropping a guard only leaves the accessor uninterpreted (UNKNOWN at
/// worst), never a fabricated proof.
fn variant_conflicted_containers(exprs: &[Expr]) -> HashSet<String> {
    let mut seen_ctors: std::collections::HashMap<String, HashSet<String>> =
        std::collections::HashMap::new();
    let mut stack: Vec<&Expr> = exprs.iter().collect();
    while let Some(e) = stack.pop() {
        if let ExprValue::DatatypeSelector { selector_name, expr: container, .. } = e.value()
            && let SortInner::Datatype(dt) = container.sort().inner()
            && dt.constructors.len() > 1
            && let Some(cons) = dt.constructors.iter().find(|c| c.has_field(selector_name))
        {
            seen_ctors
                .entry(container_identity(container))
                .or_default()
                .insert(cons.name.clone());
        }
        stack.extend(e.value().children());
    }
    seen_ctors.into_iter().filter(|(_, cs)| cs.len() > 1).map(|(k, _)| k).collect()
}

pub(in crate::codegen_ay) fn collect_constructor_guards(exprs: &[Expr]) -> Vec<Expr> {
    let mut guards = Vec::new();
    // Deduplicate by container pointer identity + constructor name to avoid
    // emitting redundant guards when the same variable is accessed multiple
    // times in one block. We use the raw pointer of the container's ExprValue
    // Arc as a cheap identity key.
    let mut seen: HashSet<(usize, String)> = HashSet::new();
    // Constructors this block PINS by a sibling constraint. See
    // `pinned_constructors`.
    let pinned = pinned_constructors(exprs);
    let conflicted = variant_conflicted_containers(exprs);
    for expr in exprs {
        collect_guards_recursive(expr, &mut guards, &mut seen, &pinned, &conflicted);
    }
    if !guards.is_empty() {
        debug!(
            "constructor_guard: emitted {} guard(s) from {} constraints",
            guards.len(),
            exprs.len()
        );
    }
    guards
}

/// Recursively walk an expression tree, collecting constructor tester guards
/// for every DatatypeSelector node whose container is a multi-constructor datatype.
/// Variables this block binds directly to a datatype constructor, as
/// `var name -> constructor name`.
///
/// A block that CONSTRUCTS its value (`let flag = MyEnum::Flag1(..)`) pins the
/// variant just as firmly as one that switched on it, but the binding lives in
/// a SIBLING constraint (`Eq(var, Flag1_MyEnum(..))`) rather than in the
/// container expression, so the syntactic `DatatypeConstructor` check below
/// cannot see it. Emitting `((_ is Flag2) v)` next to `v = Flag1(..)` makes the
/// block UNSAT, every path infeasible and the harness VACUOUS — which is what
/// `size_of_val(&flag)` on any multi-variant enum did.
///
/// A name bound to two different constructors is dropped: that is not a pin.
///
/// The whole constructor EXPRESSION is kept, not just its name, so that a
/// selector chain rooted at a pinned variable resolves too — `Flag2(0, None)`
/// pins `v`, which in turn pins `Flag2_field_1(v)` to `None`. Without that,
/// `MyEnum::Flag2(0, None)` still emitted `((_ is Some) (Flag2_field_1 v))`
/// and stayed vacuous while `Flag1(Some(true))` was already fixed.
fn pinned_constructors(exprs: &[Expr]) -> std::collections::HashMap<String, Expr> {
    let mut pinned: std::collections::HashMap<String, Expr> = std::collections::HashMap::new();
    let mut conflicted: Vec<String> = Vec::new();
    for expr in exprs {
        let ExprValue::Eq(lhs, rhs) = expr.value() else { continue };
        for (var_side, val_side) in [(lhs, rhs), (rhs, lhs)] {
            let (ExprValue::Var { name }, ExprValue::DatatypeConstructor { constructor_name, .. }) =
                (var_side.value(), val_side.value())
            else {
                continue;
            };
            if let Some(prev) = pinned.insert(name.to_string(), val_side.clone())
                && !matches!(
                    prev.value(),
                    ExprValue::DatatypeConstructor { constructor_name: p, .. }
                        if p == constructor_name
                )
            {
                conflicted.push(name.to_string());
            }
        }
    }
    for name in conflicted {
        pinned.remove(&name);
    }
    pinned
}

/// Resolve `container` to the constructor it must hold, following pinned
/// variables and selecting through their fields. `None` when the block does not
/// decide it.
fn resolve_pinned_constructor(
    container: &Expr,
    pinned: &std::collections::HashMap<String, Expr>,
) -> Option<Expr> {
    match container.value() {
        ExprValue::DatatypeConstructor { .. } => Some(container.clone()),
        ExprValue::Var { name } => pinned.get(&**name).cloned(),
        ExprValue::DatatypeSelector { selector_name, expr: inner, .. } => {
            let resolved = resolve_pinned_constructor(inner, pinned)?;
            let ExprValue::DatatypeConstructor { constructor_name, args, .. } = resolved.value()
            else {
                return None;
            };
            // Find the field's position within its own constructor.
            let SortInner::Datatype(dt) = inner.sort().inner() else { return None };
            let cons = dt.constructors.iter().find(|c| c.name == **constructor_name)?;
            let idx = cons.fields.iter().position(|f| *f.name == **selector_name)?;
            args.get(idx).cloned()
        }
        _ => None,
    }
}

fn collect_guards_recursive(
    expr: &Expr,
    guards: &mut Vec<Expr>,
    seen: &mut HashSet<(usize, String)>,
    pinned: &std::collections::HashMap<String, Expr>,
    conflicted: &HashSet<String>,
) {
    match expr.value() {
        ExprValue::DatatypeSelector { datatype_name, selector_name, expr: container } => {
            // Check if the container is a multi-constructor datatype.
            if let SortInner::Datatype(dt) = container.sort().inner() {
                if dt.constructors.len() > 1 {
                    // Find which constructor owns this selector.
                    if let Some(cons) = dt.constructors.iter().find(|c| c.has_field(selector_name))
                    {
                        // Skip guard when container is a known DT constant (#3896).
                        // If the container is a DatatypeConstructor, the variant is
                        // statically known. Emitting a guard for a mismatched
                        // constructor (e.g., `((_ is Some) None)`) makes the rule
                        // body vacuously false, producing a false PROOF. When the
                        // constructor matches, the guard is trivially true and adds
                        // no information. Either way, skip.
                        // Known when the container IS a constructor, or when the
                        // block's own constraints decide it — directly, or through
                        // a selector chain rooted at a pinned variable. Same
                        // reasoning either way: the variant is already decided, so
                        // a matching guard adds nothing and a mismatched one is
                        // FALSE and makes the whole block unsatisfiable.
                        let container_is_known_constant =
                            resolve_pinned_constructor(container, pinned).is_some();
                        if !container_is_known_constant {
                            let guard =
                                literal_constructor_guard(container, datatype_name, &cons.name)
                                    .unwrap_or_else(|| {
                                        container.clone().is_constructor(
                                            datatype_name.clone(),
                                            cons.name.clone(),
                                        )
                                    });
                            // Skip guards that are semantically constant. A
                            // constant-TRUE guard adds no information; a
                            // constant-FALSE guard (e.g. `((_ is B_Foo) …)` on a
                            // value statically known to be `A_Foo`) would inject
                            // a vacuously-false constraint into the rule body,
                            // making a genuinely-reachable block/assertion
                            // unreachable → false PROOF. `simplify_bool_ite` can
                            // yield `not(not(false))`, which is a `Not` node, not
                            // a bare `BoolConst`, so peel nested negations before
                            // deciding. Part of the multi-variant-flattened enum
                            // downcast-guard fix.
                            // SOUNDNESS: a guard may only be asserted when the
                            // block's path already establishes the container's
                            // constructor (the #3207 case: a plain state var the
                            // block switched on). When the container is an `Ite`,
                            // the constructor is DATA-DEPENDENT — a reconstructed
                            // flattened enum `ite(tag, Ok(..), Err(..))` — so
                            // `((_ is Err) …)` folds to `not(tag)` (via
                            // `literal_constructor_guard`), which is not a
                            // constant and therefore survives the check below.
                            // Asserting it PRUNES the complementary `tag` path:
                            // observed as `OnceCell::set` making everything after
                            // it unreachable, so an `assert!(false)` "verifies".
                            // Same defect as the #3896 constant case, only
                            // data-dependent instead of static. Dropping the guard
                            // only leaves the accessor uninterpreted (UNKNOWN at
                            // worst) — never a fabricated proof.
                            let container_is_data_dependent =
                                matches!(container.value(), ExprValue::Ite { .. });
                            if container_is_data_dependent || peel_bool_const(&guard).is_some() {
                                collect_guards_recursive(container, guards, seen, pinned, conflicted);
                                return;
                            }
                            // Dedup by container identity (pointer) + constructor name.
                            // This correctly handles multiple variables of the same type
                            // (different containers get different guards) while avoiding
                            // duplicates for the same container accessed via different
                            // fields.
                            // The block reads this container through selectors of
                            // MORE THAN ONE constructor, so its variant is not
                            // established and any fact-form guard is arbitrary.
                            // Asserting one prunes the complementary path.
                            if conflicted.contains(&container_identity(container)) {
                                debug!(
                                    "constructor_guard: SKIP ((_ is {}) ...) - container is \
                                     variant-conflicted (selectors of >1 constructor)",
                                    cons.name
                                );
                                collect_guards_recursive(container, guards, seen, pinned, conflicted);
                                return;
                            }
                            let container_ptr = std::ptr::from_ref(container.value()) as usize;
                            let key = (container_ptr, cons.name.clone());
                            if seen.insert(key) {
                                debug!(
                                    "constructor_guard: adding ((_ is {}) ...) for selector {} on {}",
                                    cons.name, selector_name, datatype_name
                                );
                                guards.push(guard);
                            }
                        }
                    }
                }
            }
            // Recurse into the container expression (may have nested selectors).
            collect_guards_recursive(container, guards, seen, pinned, conflicted);
        }
        // For all other variants, recurse into sub-expressions.
        ExprValue::Not(e)
        | ExprValue::BvNeg(e)
        | ExprValue::BvNot(e)
        | ExprValue::IntNeg(e)
        | ExprValue::IntToReal(e)
        | ExprValue::RealToInt(e)
        | ExprValue::IsInt(e)
        | ExprValue::RealNeg(e)
        | ExprValue::BvNegNoOverflow(e)
        | ExprValue::BvZeroExtend { expr: e, .. }
        | ExprValue::BvSignExtend { expr: e, .. }
        | ExprValue::BvExtract { expr: e, .. }
        | ExprValue::ConstArray { value: e, .. } => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        ExprValue::And(es) | ExprValue::Or(es) | ExprValue::Distinct(es) => {
            for e in es {
                collect_guards_recursive(e, guards, seen, pinned, conflicted);
            }
        }
        ExprValue::Eq(a, b)
        | ExprValue::Xor(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvConcat(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b)
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
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            collect_guards_recursive(cond, guards, seen, pinned, conflicted);
            // Part of #3886: When the ITE condition is a DatatypeTester
            // `((_ is C) container)`, the then-branch is already guarded
            // by the tester — selectors inside it are only evaluated when
            // the tester holds. Emitting standalone top-level guards for
            // those selectors is redundant at best, and produces vacuously
            // false constraints when the tester evaluates to false at
            // runtime. Example: `(ite ((_ is Some) (fld_data x)) (value
            // (fld_data x)) #x0...)` — the `value` selector is safe
            // inside the then-branch, but a standalone guard `((_ is Some)
            // (fld_data x))` injected into the rule body kills the rule
            // when x.data is None, causing false PROOF.
            if !matches!(cond.value(), ExprValue::DatatypeTester { .. }) {
                collect_guards_recursive(then_expr, guards, seen, pinned, conflicted);
            }
            collect_guards_recursive(else_expr, guards, seen, pinned, conflicted);
        }
        ExprValue::Select { array, index } => {
            collect_guards_recursive(array, guards, seen, pinned, conflicted);
            collect_guards_recursive(index, guards, seen, pinned, conflicted);
        }
        ExprValue::Store { array, index, value } => {
            collect_guards_recursive(array, guards, seen, pinned, conflicted);
            collect_guards_recursive(index, guards, seen, pinned, conflicted);
            collect_guards_recursive(value, guards, seen, pinned, conflicted);
        }
        ExprValue::DatatypeConstructor { args, .. } => {
            for arg in args {
                collect_guards_recursive(arg, guards, seen, pinned, conflicted);
            }
        }
        ExprValue::DatatypeTester { expr: e, .. } => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        ExprValue::FuncApp { args, .. } => {
            for arg in args {
                collect_guards_recursive(arg, guards, seen, pinned, conflicted);
            }
        }
        ExprValue::Forall { body, .. } | ExprValue::Exists { body, .. } => {
            collect_guards_recursive(body, guards, seen, pinned, conflicted);
        }
        // Leaf nodes: no sub-expressions to recurse into.
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_)
        | ExprValue::Var { .. } => {}
        // Sort conversions: recurse into sub-expression (soundness-critical).
        // Bv2Int/Int2Bv wrap DatatypeSelector in production CHC encoding.
        ExprValue::Bv2Int(e) | ExprValue::Int2Bv(e, _) => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        // FP unary operations: recurse into sub-expression.
        ExprValue::FpAbs(e)
        | ExprValue::FpNeg(e)
        | ExprValue::FpIsNaN(e)
        | ExprValue::FpIsInfinite(e)
        | ExprValue::FpIsZero(e)
        | ExprValue::FpIsNormal(e)
        | ExprValue::FpIsSubnormal(e)
        | ExprValue::FpIsPositive(e)
        | ExprValue::FpIsNegative(e)
        | ExprValue::FpToReal(e) => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        // FP operations with RoundingMode + single expression.
        ExprValue::FpSqrt(_, e)
        | ExprValue::FpRoundToIntegral(_, e)
        | ExprValue::FpToSbv(_, e, _)
        | ExprValue::FpToUbv(_, e, _)
        | ExprValue::BvToFp(_, e, _, _)
        | ExprValue::BvToFpUnsigned(_, e, _, _)
        | ExprValue::FpToFp(_, e, _, _) => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        // FP binary operations (plain two-expr).
        ExprValue::FpRem(a, b)
        | ExprValue::FpMin(a, b)
        | ExprValue::FpMax(a, b)
        | ExprValue::FpEq(a, b)
        | ExprValue::FpLt(a, b)
        | ExprValue::FpLe(a, b)
        | ExprValue::FpGt(a, b)
        | ExprValue::FpGe(a, b) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
        }
        // FP binary operations with RoundingMode.
        ExprValue::FpAdd(_, a, b)
        | ExprValue::FpSub(_, a, b)
        | ExprValue::FpMul(_, a, b)
        | ExprValue::FpDiv(_, a, b) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
        }
        // FP ternary operations.
        ExprValue::FpFromBvs(a, b, c) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
            collect_guards_recursive(c, guards, seen, pinned, conflicted);
        }
        ExprValue::FpFma(_, a, b, c) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
            collect_guards_recursive(c, guards, seen, pinned, conflicted);
        }
        // FP leaf constants: no sub-expressions.
        ExprValue::FpPlusInfinity { .. }
        | ExprValue::FpMinusInfinity { .. }
        | ExprValue::FpNaN { .. }
        | ExprValue::FpPlusZero { .. }
        | ExprValue::FpMinusZero { .. } => {}
        // String unary operations.
        ExprValue::StrLen(e)
        | ExprValue::StrToInt(e)
        | ExprValue::StrFromInt(e)
        | ExprValue::StrToRe(e) => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        // String binary operations.
        ExprValue::StrConcat(a, b)
        | ExprValue::StrAt(a, b)
        | ExprValue::StrContains(a, b)
        | ExprValue::StrPrefixOf(a, b)
        | ExprValue::StrSuffixOf(a, b)
        | ExprValue::StrInRe(a, b) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
        }
        // String ternary operations.
        ExprValue::StrSubstr(a, b, c)
        | ExprValue::StrIndexOf(a, b, c)
        | ExprValue::StrReplace(a, b, c)
        | ExprValue::StrReplaceAll(a, b, c) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
            collect_guards_recursive(c, guards, seen, pinned, conflicted);
        }
        // Regex operations.
        ExprValue::ReStar(e) | ExprValue::RePlus(e) => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        ExprValue::ReUnion(a, b) | ExprValue::ReConcat(a, b) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
        }
        // Sequence leaf: no sub-expressions.
        ExprValue::SeqEmpty(_) => {}
        // Sequence unary operations.
        ExprValue::SeqUnit(e) | ExprValue::SeqLen(e) => {
            collect_guards_recursive(e, guards, seen, pinned, conflicted);
        }
        // Sequence binary operations.
        ExprValue::SeqConcat(a, b)
        | ExprValue::SeqNth(a, b)
        | ExprValue::SeqContains(a, b)
        | ExprValue::SeqPrefixOf(a, b)
        | ExprValue::SeqSuffixOf(a, b) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
        }
        // Sequence ternary operations.
        ExprValue::SeqExtract(a, b, c)
        | ExprValue::SeqIndexOf(a, b, c)
        | ExprValue::SeqReplace(a, b, c) => {
            collect_guards_recursive(a, guards, seen, pinned, conflicted);
            collect_guards_recursive(b, guards, seen, pinned, conflicted);
            collect_guards_recursive(c, guards, seen, pinned, conflicted);
        }
        // Catch-all for future ExprValue variants (#[non_exhaustive]).
        // All 146 known variants are handled explicitly above.
        // If AY adds new variants with Expr fields, this will silently skip them.
        // Prefer adding explicit arms above when new variants are observed.
        _ => {
            debug!("constructor_guard: unhandled ExprValue variant in guard collection");
        }
    }
}

/// Fold a guard expression to a boolean constant when it is semantically
/// constant, peeling nested `Not` negations. `simplify_bool_ite` can emit
/// `not(not(false))` (a `Not` node wrapping a `BoolConst`) for a statically
/// decided constructor test; a bare `matches!(_, BoolConst(_))` check misses it.
fn peel_bool_const(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(b) => Some(*b),
        ExprValue::Not(inner) => peel_bool_const(inner).map(|b| !b),
        _ => None,
    }
}

fn literal_constructor_guard(container: &Expr, dt_name: &str, cons_name: &str) -> Option<Expr> {
    // Avoid `((_ is C) (ite cond (A ...) (B ...)))` guards; PDR struggles
    // with the datatype tester, while the equivalent scalar condition is direct.
    match container.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = literal_constructor_branch_guard(then_expr, dt_name, cons_name)?;
            let else_guard = literal_constructor_branch_guard(else_expr, dt_name, cons_name)?;
            Some(simplify_bool_ite(cond.clone(), then_guard, else_guard))
        }
        _ => None,
    }
}

fn literal_constructor_branch_guard(expr: &Expr, dt_name: &str, cons_name: &str) -> Option<Expr> {
    match expr.value() {
        ExprValue::DatatypeConstructor { datatype_name, constructor_name, .. } => {
            (datatype_name == dt_name).then(|| Expr::bool_const(constructor_name == cons_name))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = literal_constructor_branch_guard(then_expr, dt_name, cons_name)?;
            let else_guard = literal_constructor_branch_guard(else_expr, dt_name, cons_name)?;
            Some(simplify_bool_ite(cond.clone(), then_guard, else_guard))
        }
        _ => None,
    }
}

fn simplify_bool_ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    match (bool_const_value(&then_expr), bool_const_value(&else_expr)) {
        (Some(true), Some(false)) => cond,
        (Some(false), Some(true)) => cond.not(),
        (Some(true), Some(true)) => Expr::bool_const(true),
        (Some(false), Some(false)) => Expr::bool_const(false),
        _ => Expr::ite(cond, then_expr, else_expr),
    }
}

fn bool_const_value(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(value) => Some(*value),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::collect_constructor_guards;
    use ay_bindings::{Expr, Sort};
    use trust_mc_codegen_types::names::enum_sort;

    fn result_sort() -> Sort {
        enum_sort(
            "Result_t_u32",
            vec![("Ok_Result", vec![]), ("Err_Result", vec![("Err_field_0", Sort::bitvec(32))])],
        )
    }

    /// A reconstructed flattened enum is `ite(tag, Ok(..), Err(..))`. Applying an
    /// `Err` selector to it must NOT emit a tester guard: `literal_constructor_guard`
    /// folds `((_ is Err) …)` to `not(tag)`, which is not a constant and so escapes
    /// the `peel_bool_const` net — asserting it as a rule-body constraint DELETES the
    /// whole `tag` (Ok) path. Live symptom: `OnceCell::set` made every statement
    /// after it unreachable, so an `assert!(false)` following it "verified".
    #[test]
    fn skips_guard_for_data_dependent_ite_container() {
        let sort = result_sort();
        let ok = Expr::datatype_constructor("Result_t_u32", "Ok_Result", vec![], sort.clone());
        let err = Expr::datatype_constructor(
            "Result_t_u32",
            "Err_Result",
            vec![Expr::bitvec_const(7u64, 32)],
            sort,
        );
        // The container's constructor is decided by a symbolic tag, not by the path.
        let reconstructed = Expr::ite(Expr::var("tag", Sort::bool()), ok, err);
        let selector = reconstructed.field_select("Result_t_u32", "Err_field_0", Sort::bitvec(32));

        let guards = collect_constructor_guards(&[selector.eq(Expr::bitvec_const(0u64, 32))]);

        assert!(
            guards.is_empty(),
            "must NOT assert `not(tag)` for a tag-selected container — it prunes the Ok path, \
             got {guards:?}"
        );
    }

    /// The #3207 case is unchanged: a plain state var container still gets its
    /// tester guard, so PDR keeps treating the accessor as interpreted.
    #[test]
    fn still_emits_guard_for_plain_var_container() {
        let sort = result_sort();
        let container = Expr::var("r", sort);
        let selector = container.field_select("Result_t_u32", "Err_field_0", Sort::bitvec(32));

        let guards = collect_constructor_guards(&[selector.eq(Expr::bitvec_const(0u64, 32))]);

        assert_eq!(guards.len(), 1, "symbolic var container still needs its is_constructor guard");
    }
}

#[cfg(test)]
mod variant_conflict_tests {
    use super::collect_constructor_guards;
    use ay_bindings::{Expr, Sort};
    use trust_mc_codegen_types::names::enum_sort;

    fn result_sort() -> Sort {
        enum_sort(
            "Result_t_u32",
            vec![
                ("Ok_Result", vec![("Ok_field_0", Sort::bitvec(8))]),
                ("Err_Result", vec![("Err_field_0", Sort::bitvec(32))]),
            ],
        )
    }

    /// A container read through selectors of TWO different constructors has an
    /// UNDECIDED variant, so no fact-form guard may be asserted for it.
    ///
    /// Regression guard for a VACUOUS-verdict bug. `find().is_ok()` on a
    /// `Result` makes the encoder materialise BOTH payloads at a merge point
    /// (`Ok(..)` from one predecessor, `Err(..)` from another). Emitting
    /// `((_ is Err) v)` as a FACT there made the block's ONLY outgoing edge
    /// infeasible, so every check became unreachable and the harness reported
    /// `[AY:VACUOUS:unsat-assumption]`. `Repr/check_repr`, `Repr/issue_837` and
    /// `Enum/multiple_never` all had exactly this shape.
    ///
    /// The two candidate guards are mutually exclusive, so asserting EITHER is
    /// an arbitrary choice that deletes the complementary path. Same rule
    /// `pinned_constructors` already applies to bindings.
    #[test]
    fn no_guard_when_container_is_variant_conflicted() {
        let sort = result_sort();
        let v = Expr::var("_v", sort);
        let ok_sel = v.clone().field_select("Result_t_u32", "Ok_field_0", Sort::bitvec(8));
        let err_sel = v.field_select("Result_t_u32", "Err_field_0", Sort::bitvec(32));

        let guards = collect_constructor_guards(&[
            ok_sel.eq(Expr::bitvec_const(0u64, 8)),
            err_sel.eq(Expr::bitvec_const(0u64, 32)),
        ]);

        assert!(
            guards.is_empty(),
            "a container read through Ok_field_0 AND Err_field_0 has an undecided variant; \
             asserting either guard prunes the complementary path, got {guards:?}"
        );
    }

    /// The complement, so the fix stays narrow: selectors of a SINGLE
    /// constructor still emit their guard (#3207 — PDR needs the tester to
    /// treat the accessor as interpreted). An earlier, blunter guard-dropping
    /// attempt broke exactly this.
    #[test]
    fn single_constructor_container_still_guarded() {
        let sort = result_sort();
        let v = Expr::var("_v", sort);
        let err_sel = v.field_select("Result_t_u32", "Err_field_0", Sort::bitvec(32));

        let guards = collect_constructor_guards(&[err_sel.eq(Expr::bitvec_const(0u64, 32))]);

        assert_eq!(
            guards.len(),
            1,
            "one constructor's selectors must still emit their guard (#3207)"
        );
    }
}
