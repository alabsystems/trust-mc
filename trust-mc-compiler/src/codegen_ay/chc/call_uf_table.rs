// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Uninterpreted-function summaries for CALLS in the CHC lane, encoded as a
//! frozen congruent table (Part of #4270 / TL18).
//!
//! # The construct
//!
//! A call `d := f(a1..an)` whose callee the encoder cannot translate precisely
//! wants the standard EUF model: `f` is an *arbitrary* symbol (the environment
//! picks it, not the solver), and two applications with equal arguments yield
//! equal results (congruence). SMT-LIB spells that `(declare-fun f (S1..Sn) R)`
//! with `R != Bool`.
//!
//! `ay-chc` cannot parse that. `crates/ay-chc/src/parser/commands.rs` rejects
//! any `declare-fun` whose return sort is not `Bool` ("Non-predicate function
//! declaration: '<name>' with return sort <S>. Only Bool-returning functions
//! (predicates) are supported in ay-chc."), and the error aborts the parse of
//! the WHOLE problem — one such declaration costs the harness its entire
//! verification. Nor is there a global-constant escape hatch: `declare-const`
//! is an alias for `declare-var` there (`commands.rs`: `"declare-var" |
//! "declare-const"`), and any free symbol resolves to a `ChcVar`, i.e. a
//! *per-clause* universally quantified variable. Two calls always live in two
//! different Horn rules, so "reuse the same free variable" gives NO sharing:
//! it degenerates to independent havocs.
//!
//! # The encoding
//!
//! The only value that is shared between two Horn rules is a value threaded
//! through the relation signature. So the UF is a FROZEN state column:
//!
//! ```text
//! call_uf_tbl : Array(BV128 -> BV64)          ; never modified, never constrained
//! d := extract(w-1, 0, select(call_uf_tbl, tag(32) ++ zext(a1 ++ .. ++ an, 96)))
//! ```
//!
//! This is exactly the mechanism `float_binop_table.rs` already uses for
//! symbolic float arithmetic, applied to calls. The table is pushed as a
//! state-var pair and never marked modified, so `build_output_args` passes the
//! input variable straight through to every successor head: along any single
//! trace all rules see the SAME table. Two calls with the same tag and the same
//! argument values therefore select the same entry and get the same value —
//! congruence — while different traces are free to see different tables.
//!
//! Key injectivity (mandatory — a colliding key would ASSERT an equality that
//! need not hold, which over-constrains and can fabricate a proof):
//!   * the tag occupies the fixed high 32 bits, so distinct callees never
//!     collide regardless of their argument widths;
//!   * tags are handed out sequentially per VC from `ChcCtx::call_uf_tags`,
//!     keyed on the callee's MANGLED name — monomorphisation-unique, so
//!     `f::<i32>` and `f::<u32>` never share a tag;
//!   * within one tag the argument widths are fixed by the monomorphised
//!     signature, so `zero_extend` of the concatenation is injective.
//! A call whose arguments do not fit in 96 bits, or whose return does not fit
//! in 64, is refused (the caller keeps its sound havoc) rather than truncated.
//!
//! # SOUNDNESS — the gate, not the machinery
//!
//! The table itself is never constrained anywhere (not in the entry rule, not
//! in any transition), so the real function is one interpretation of it and any
//! property proven over ALL interpretations holds under the real semantics.
//! That much is free.
//!
//! What is NOT free is the right to model a callee as a function of its
//! arguments at all. `codegen_call_foreign.rs` records the counterexample:
//!
//! ```c
//! static uint32_t c;
//! uint32_t takes_int(uint32_t i) { return i + c++; }
//! ```
//!
//! By-value scalar prototype, and yet `takes_int(x) != takes_int(x)`. A UF over
//! the arguments PROVES the two calls equal — a fabricated proof. The same trap
//! closed this lane for alloc/RNG/IO in
//! `codegen_call_cmp_string/fallback_dispatch.rs`, whose demonstration on
//! `d1 := g(x); d2 := g(x); if d1 != d2 { error }` is: UF summary -> sat (a
//! PROOF that d1 == d2), havoc -> unsat (the error is reachable, the sound
//! answer).
//!
//! So the summary is emitted ONLY behind `established_pure_scalar_callee`,
//! which does not look at the signature shape — it reads the callee's MIR body
//! and requires, transitively (bounded depth, no cycles):
//!
//! 1. by-value scalar parameters and return (no reference, raw pointer, ADT,
//!    tuple, array, slice, `str`, `dyn`, fn-pointer or closure anywhere in the
//!    signature) — an indirect argument would make the result depend on memory
//!    the key does not contain, so equal keys would not imply equal results;
//! 2. no `Deref` projection anywhere in the body, and no operand constant of
//!    reference or raw-pointer type — the body cannot read through a pointer,
//!    so it cannot read a `static`, a thread local or any interior-mutable
//!    cell (this is what kills the `takes_int` counterexample: `c++` is a
//!    static access);
//! 3. no `Rvalue::Ref` / `AddressOf` / `Reborrow` / `ThreadLocalRef` /
//!    `CopyForDeref` / `Len`, and no `StatementKind::Intrinsic` — nothing that
//!    creates or follows a pointer, and no `copy_nonoverlapping`;
//! 4. no `Assert`, `Unreachable`, `Abort`, `Resume`, `Drop`, `InlineAsm`
//!    terminator, and no diverging `Call` — the callee has NO panicking path,
//!    so summarising it drops no failure the caller should have seen. This is
//!    the clause that makes the site blessable rather than merely more precise:
//!    an overflow-checked `x + 1` lowers to `CheckedBinaryOp` + `Assert`, and
//!    is therefore REFUSED, because a UF would silently swallow its overflow
//!    panic (a missed bug);
//! 5. every nested `Call` resolves to a callee that itself passes 1-4, or to
//!    one of the total, pure bit intrinsics in `PURE_TOTAL_INTRINSICS` (the
//!    only bodiless callees accepted; `ctlz_nonzero`, `unchecked_*` and
//!    `exact_div` are deliberately absent — they carry UB).
//!
//! A callee passing 1-5 has no observable effect other than its return value,
//! and that value is a mathematical function of the argument values. Loops are
//! allowed: a non-terminating callee makes the model reach the successor where
//! the real program does not, which ADDS behaviours and is therefore
//! conservative for safety.
//!
//! # Cost control
//!
//! An Array-sorted frame column is the most expensive thing to add to a Horn
//! relation (#4259), so the pre-scan is deliberately strict. The table is
//! declared only when the harness body applies the SAME symbol at least TWICE —
//! the only situation congruence can pay for — and, for the call lane, only for
//! a callee the precise inline lane has already given up on (too big for
//! `chc_inline_effective_block_limit`, or self-recursive so the MIR
//! `FunctionInlinePass` skips it). Math intrinsics with an exact BV encoding
//! (`fabs`, `floor`, `ceil`, `trunc`, `round`, `copysign`, `minnum`, `maxnum`)
//! are excluded outright: they are already precise.
//!
//! MEASURED, and the reason the two-site rule exists: with a one-site rule
//! `Intrinsics/Math/Arith/powi.rs` went 2/2 -> 0/2 (both harnesses lost to
//! solver Timeout / SolverError) for a column its single `x.powi(2)` could
//! never use.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    Body, LocalDecl, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use crate::codegen_ay::shared::count_effective_blocks;

/// Input-side name of the frozen congruent call-summary table.
pub(in crate::codegen_ay::chc) const CALL_UF_TBL: &str = "call_uf_tbl";
/// Output-side name (identity-threaded: the table is never marked modified).
pub(in crate::codegen_ay::chc) const CALL_UF_TBL_OUT: &str = "call_uf_tbl__out";

/// Width of the callee tag in the table key (fixed HIGH bits — see module doc).
const TAG_WIDTH: u32 = 32;
/// Width of the zero-extended argument concatenation in the table key.
const ARG_WIDTH: u32 = 96;
/// Width of a table VALUE. Narrower returns take the low bits.
const VALUE_WIDTH: u32 = 64;
/// Bound on the transitive purity walk. A cycle (direct or mutual recursion)
/// simply exhausts the budget and the callee is refused.
const MAX_PURITY_DEPTH: usize = 3;

/// Bodiless callees accepted by the purity walk: compiler intrinsics that are
/// TOTAL (defined on every input, no UB) and PURE (a function of the arguments
/// alone). Deliberately excludes `ctlz_nonzero`, `cttz_nonzero`, `unchecked_*`
/// and `exact_div`, all of which carry UB the summary would swallow.
const PURE_TOTAL_INTRINSICS: &[&str] = &[
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "saturating_add",
    "saturating_sub",
    "bswap",
    "bitreverse",
    "ctpop",
    "ctlz",
    "cttz",
    "rotate_left",
    "rotate_right",
];

/// Sort of the frozen congruent call-summary table.
pub(in crate::codegen_ay::chc) fn call_uf_table_sort() -> Sort {
    Sort::array(Sort::bitvec(TAG_WIDTH + ARG_WIDTH), Sort::bitvec(VALUE_WIDTH))
}

/// `true` when `ty` is a by-value scalar the key can carry losslessly.
fn ty_is_uf_scalar(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)
        )
    )
}

/// `true` when the place walks through a pointer. Field/index/downcast
/// projections stay inside the callee's own frame and are fine.
fn place_has_indirection(place: &Place) -> bool {
    place.projection.iter().any(|elem| matches!(elem, ProjectionElem::Deref))
}

/// `true` when reading this operand cannot touch memory outside the frame.
///
/// A constant of reference or raw-pointer type is refused: that is how a
/// `static`, a promoted, or a `&str` literal enters a body.
fn operand_is_pure(operand: &Operand, _locals: &[LocalDecl]) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => !place_has_indirection(place),
        Operand::Constant(konst) => {
            !matches!(konst.ty().kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
        }
    }
}

/// `true` when the rvalue reads only frame-local, pointer-free state.
fn rvalue_is_pure(rvalue: &Rvalue, locals: &[LocalDecl]) -> bool {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Repeat(operand, _) | Rvalue::UnaryOp(_, operand) => {
            operand_is_pure(operand, locals)
        }
        // `sizeof`/`alignof`/`offsetof` — compile-time constants.
        Rvalue::NullaryOp(_) => true,
        Rvalue::Cast(_, operand, _) => operand_is_pure(operand, locals),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_is_pure(lhs, locals) && operand_is_pure(rhs, locals)
        }
        Rvalue::Aggregate(_, operands) => {
            operands.iter().all(|operand| operand_is_pure(operand, locals))
        }
        Rvalue::Discriminant(place) => !place_has_indirection(place),
        // Everything that creates or follows a pointer, reads a thread local,
        // or reads slice metadata.
        Rvalue::Ref(..)
        | Rvalue::AddressOf(..)
        | Rvalue::ShallowInitBox(..)
        | Rvalue::ThreadLocalRef(_)
        | Rvalue::CopyForDeref(_)
        | Rvalue::Len(_) => false,
    }
}

/// Resolve a `Call` terminator's callee operand to a monomorphised instance.
fn resolve_call_instance(func: &Operand, locals: &[LocalDecl]) -> Option<Instance> {
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(locals).ok()?.kind() else {
        return None;
    };
    Instance::resolve(def, &args).ok()
}

/// The purity walk over one MIR body. See the module doc for the clause list.
fn body_is_pure(body: &Body, path: &mut Vec<String>) -> bool {
    let locals = body.locals();
    for block in &body.blocks {
        for stmt in &block.statements {
            let ok = match &stmt.kind {
                StatementKind::Assign(place, rvalue) => {
                    !place_has_indirection(place) && rvalue_is_pure(rvalue, locals)
                }
                StatementKind::SetDiscriminant { place, .. }
                | StatementKind::FakeRead(_, place)
                | StatementKind::Retag(_, place)
                | StatementKind::PlaceMention(place)
                | StatementKind::AscribeUserType { place, .. } => !place_has_indirection(place),
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Coverage(_)
                | StatementKind::ConstEvalCounter
                | StatementKind::Nop => true,
                // `copy_nonoverlapping` / `assume` — memory intrinsics.
                StatementKind::Intrinsic(_) => false,
            };
            if !ok {
                return false;
            }
        }
        let ok = match &block.terminator.kind {
            TerminatorKind::Goto { .. } | TerminatorKind::Return => true,
            TerminatorKind::SwitchInt { discr, .. } => operand_is_pure(discr, locals),
            TerminatorKind::Call { func, args, destination, target: Some(_), .. } => {
                !place_has_indirection(destination)
                    && args.iter().all(|arg| operand_is_pure(arg, locals))
                    && resolve_call_instance(func, locals)
                        .is_some_and(|inner| instance_is_pure(&inner, path))
            }
            // Assert (a panicking path the summary would swallow), Drop,
            // InlineAsm, Unreachable, Abort, Resume, diverging Call.
            _ => false,
        };
        if !ok {
            return false;
        }
    }
    true
}

/// `true` when this monomorphised instance is an ESTABLISHED pure function of
/// its arguments: scalar signature, effect-free body, no panicking path.
///
/// `path` is the chain of callees currently being walked, by mangled name. A
/// call back to a name already on the path is a RECURSIVE back-edge and is
/// accepted co-inductively: every other construct on the cycle has been (or is
/// being) checked, so the only thing recursion can add is non-termination —
/// and a callee that never returns makes the model reach the successor where
/// the real program does not, which ADDS behaviours and is conservative for
/// safety. Self-recursion is exactly the shape that survives the MIR
/// `FunctionInlinePass` (it skips self-recursive callees), so refusing it
/// would leave the gate with nothing to admit.
fn instance_is_pure(instance: &Instance, path: &mut Vec<String>) -> bool {
    let key = instance.mangled_name().to_string();
    if path.iter().any(|seen| *seen == key) {
        return true;
    }
    if path.len() > MAX_PURITY_DEPTH {
        return false;
    }
    let Some(body) = instance.body() else {
        // The ONLY bodiless callees accepted are the hand-audited total, pure
        // bit intrinsics. Everything else (foreign items, UB-carrying
        // intrinsics, shims) is refused: purity cannot be established without
        // something to read.
        let name = instance.trimmed_name();
        // Must be a COMPILER INTRINSIC by path, not merely a symbol whose last
        // segment happens to spell one: a bodiless `extern "C" fn wrapping_add`
        // would otherwise be admitted, and a foreign body can do anything.
        if !name.contains("intrinsics::") {
            return false;
        }
        return PURE_TOTAL_INTRINSICS.iter().any(|pure| {
            name.split(['<', '>', ',', ' ', '('])
                .flat_map(|part| part.split("::"))
                .any(|segment| segment == *pure)
        });
    };
    if !body.arg_locals().iter().all(|local| ty_is_uf_scalar(local.ty))
        || !ty_is_uf_scalar(body.ret_local().ty)
    {
        return false;
    }
    path.push(key);
    let pure = body_is_pure(&body, path);
    path.pop();
    pure
}

/// Math intrinsics that reach the axiom/unconstrained tiers and therefore WANT
/// a congruent term.
///
/// Deliberately excludes every intrinsic with an exact BV encoding in
/// `math_axioms::try_exact_{unary,binary}_encoding` — `fabs`, `floor`, `ceil`,
/// `trunc`, `round`, `round_ties_even`, `copysign`, `minnum`, `maxnum`. Those
/// are already `dest = f(input)` exactly, so a table entry would be dead
/// weight; and the pre-scan keys on this list, so a harness that only rounds
/// (`FloatingPoint/float_remainder.rs`, which calls `f32::abs`) does not pay an
/// Array-sorted frame column it can never use. Frame WIDTH is the cost driver
/// here (#4259), so this list is the whole cost control.
const CONGRUENT_MATH_STEMS: &[&str] =
    &["sqrt", "sin", "cos", "exp", "exp2", "log", "log2", "log10", "powf", "powi", "fma"];

/// `true` when the (normalised) intrinsic suffix is one this lane summarises.
fn is_congruent_math_suffix(suffix: &str) -> bool {
    let stem = suffix.strip_suffix("f32").or_else(|| suffix.strip_suffix("f64")).unwrap_or(suffix);
    CONGRUENT_MATH_STEMS.contains(&stem)
}

/// Canonical per-VC tag key for a math intrinsic, normalising the intrinsic
/// spelling (`std::intrinsics::sinf32`) and the method spelling
/// (`core::f32::math::sin`) of the same function onto one key.
///
/// `None` for an intrinsic outside `CONGRUENT_MATH_STEMS`, so the exactly
/// encoded rounding/sign intrinsics never build a table term.
fn math_uf_tag_key(callee_path: &str) -> Option<String> {
    let suffix = math_intrinsic_suffix(callee_path)?;
    is_congruent_math_suffix(&suffix).then(|| format!("math:{suffix}"))
}

/// The normalised intrinsic suffix (`sinf32`) of a math callee path, in either
/// the intrinsic or the method spelling.
fn math_intrinsic_suffix(callee_path: &str) -> Option<String> {
    use super::call::codegen_call_cmp_string::math::{
        F32_SUFFIXES, F64_SUFFIXES, normalize_to_intrinsic_suffix,
    };
    F32_SUFFIXES
        .iter()
        .chain(F64_SUFFIXES.iter())
        .find(|suffix| callee_path.ends_with(**suffix))
        .map(|suffix| (*suffix).to_string())
        .or_else(|| normalize_to_intrinsic_suffix(callee_path))
}

/// Public gate used by both the pre-scan and the call site.
pub(in crate::codegen_ay::chc) fn established_pure_scalar_callee(instance: &Instance) -> bool {
    instance_is_pure(instance, &mut Vec::new())
}

/// `true` when the callee calls itself — the shape the MIR `FunctionInlinePass`
/// refuses to inline, so the precise CHC lane bottoms out on it by RECURSION
/// rather than by size.
fn callee_is_self_recursive(instance: &Instance, body: &Body) -> bool {
    let self_name = instance.mangled_name();
    let locals = body.locals();
    body.blocks.iter().any(|block| {
        matches!(&block.terminator.kind, TerminatorKind::Call { func, .. }
            if resolve_call_instance(func, locals)
                .is_some_and(|inner| inner.mangled_name() == self_name))
    })
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Input-side table variable, iff the pre-scan declared it.
    ///
    /// Never returns an undeclared variable: a select over a var missing from
    /// the relation signature would be a per-rule free variable — sound (it
    /// degenerates to havoc) but silently NON-congruent, which is exactly the
    /// bug this encoding exists to avoid.
    fn call_uf_table_var(&self) -> Option<Expr> {
        let idx = self.state_var_mgr.state_var_index_by_name(CALL_UF_TBL)?;
        let (name, sort) = &self.state_var_mgr.state_vars[idx];
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Whether the pre-scan declared the table for this harness.
    ///
    /// Call sites check this BEFORE translating arguments so that a harness
    /// without the table takes a byte-identical path to the pre-#4270 encoding
    /// — `translate_operand_with_modified` can register pending declarations,
    /// and a measurement control that perturbs the thing it measures is worse
    /// than no control.
    pub(in crate::codegen_ay::chc) fn call_uf_table_declared(&self) -> bool {
        self.state_var_mgr.state_var_index_by_name(CALL_UF_TBL).is_some()
    }

    /// Stable per-VC tag for a symbol. Two symbols share a tag only if their
    /// keys are equal, i.e. only if they are the SAME function.
    fn call_uf_tag(&mut self, key: &str) -> Option<u32> {
        if let Some(tag) = self.call_uf_tags.get(key) {
            return Some(*tag);
        }
        let next = u32::try_from(self.call_uf_tags.len()).ok()?;
        // Leave head-room rather than wrap: a wrapped tag would collide.
        if next == u32::MAX {
            return None;
        }
        self.call_uf_tags.insert(key.to_string(), next);
        Some(next)
    }

    /// Build the congruent summary term for `instance(arg_exprs) -> out_sort`.
    ///
    /// `None` — caller keeps its sound havoc — when the table was not declared,
    /// when any argument or the result is not a bit-vector, or when the key
    /// would not fit (never truncated: see the injectivity note in the module
    /// doc).
    pub(in crate::codegen_ay::chc) fn call_uf_summary_term(
        &mut self,
        instance: &Instance,
        arg_exprs: &[Expr],
        out_sort: &Sort,
    ) -> Option<Expr> {
        // "fn:" namespaces the mangled name away from the "math:" keys below,
        // so the two lanes can never accidentally share a tag.
        let key = format!("fn:{}", instance.mangled_name());
        self.call_uf_summary_term_keyed(&key, arg_exprs, out_sort)
    }

    /// Congruent summary term for a PURE MATH INTRINSIC (`sin`, `sqrt`, `log`,
    /// `powf`, …).
    ///
    /// Purity is ESTABLISHED here by the intrinsic's specification, not guessed
    /// from a signature: these are mathematical functions of their arguments
    /// with no memory operand and no hidden state — precisely the fact the
    /// blessed `math_axiom_range_overapprox` fallback already rests on ("the
    /// destination is the call's ONLY effect"). Congruence only requires
    /// determinism WITHIN one execution, which holds even though the libm
    /// result is allowed to be platform-dependent.
    ///
    /// Without this the encoder cannot prove `sin(x) == sin(x)`: the two sites
    /// received independent havocs. The intrinsic and method spellings of the
    /// same function (`std::intrinsics::sinf32` and `core::f32::math::sin`)
    /// normalise to the SAME tag, so they are congruent with each other too.
    pub(in crate::codegen_ay::chc) fn math_uf_summary_term(
        &mut self,
        callee_path: &str,
        arg_exprs: &[Expr],
        out_sort: &Sort,
    ) -> Option<Expr> {
        let key = math_uf_tag_key(callee_path)?;
        self.call_uf_summary_term_keyed(&key, arg_exprs, out_sort)
    }

    fn call_uf_summary_term_keyed(
        &mut self,
        tag_key: &str,
        arg_exprs: &[Expr],
        out_sort: &Sort,
    ) -> Option<Expr> {
        let out_width = out_sort.bitvec_width()?;
        if out_width == 0 || out_width > VALUE_WIDTH {
            return None;
        }
        let mut total_arg_width = 0u32;
        for arg in arg_exprs {
            total_arg_width = total_arg_width.checked_add(arg.sort().bitvec_width()?)?;
        }
        if total_arg_width > ARG_WIDTH {
            return None;
        }
        let table = self.call_uf_table_var()?;
        let tag = self.call_uf_tag(tag_key)?;

        // tag(32) ++ zext(a1 ++ .. ++ an, 96)
        let mut payload: Option<Expr> = None;
        for arg in arg_exprs {
            payload = Some(match payload {
                Some(acc) => acc.concat(arg.clone()),
                None => arg.clone(),
            });
        }
        let payload = match payload {
            Some(bits) if total_arg_width < ARG_WIDTH => {
                bits.zero_extend(ARG_WIDTH - total_arg_width)
            }
            Some(bits) => bits,
            // Nullary callee: the tag alone identifies the (single) entry.
            None => Expr::bitvec_const(0u128, ARG_WIDTH),
        };
        let key = Expr::bitvec_const(u128::from(tag), TAG_WIDTH).concat(payload);
        let value = table.select(key);
        Some(if out_width == VALUE_WIDTH { value } else { value.extract(out_width - 1, 0) })
    }

    /// Declare the frozen congruent call-summary table for this body.
    ///
    /// Called from `collect_state_vars`. Read-only: never marked modified, so
    /// successor heads always receive the input variable (identity threading),
    /// and the entry rule leaves it unconstrained.
    pub(in crate::codegen_ay::chc) fn collect_call_uf_table_state_vars(&mut self) {
        // Measurement control ONLY (same role as
        // `TRUST_MC_NO_STRAIGHTLINE_DISCHARGE`): with the table undeclared,
        // `call_uf_table_var` returns `None`, every congruence term degenerates
        // to `None`, and both lanes fall back to the exact pre-#4270 encoding.
        // Nothing about soundness depends on it — congruence only ever removes
        // spurious counterexamples.
        if std::env::var_os("TRUST_MC_NO_CALL_UF_TABLE").is_some() {
            return;
        }
        if !self.call_uf_table_needed() {
            return;
        }
        self.push_state_var_pair(CALL_UF_TBL, CALL_UF_TBL_OUT, call_uf_table_sort());
        debug!("CHC: added congruent call-summary table (read-only, unconstrained)");
    }

    /// Pre-scan: does this harness contain a call PAIR that congruence can pay
    /// for?
    ///
    /// Congruence buys exactly one thing — two applications of the same symbol
    /// to the same argument value collapse to one term — so it is worth a frame
    /// column ONLY when the body applies the same symbol at least twice. That
    /// is not a heuristic nicety, it is the cost control: an Array-sorted state
    /// parameter is the single most expensive thing to add to a Horn relation
    /// (#4259), and a one-call-site harness would pay it for nothing.
    /// MEASURED: with a >=1 rule, `Intrinsics/Math/Arith/powi.rs` (one
    /// `x.powi(2)` per harness, proof `x^2 >= 0` needing only the even-power
    /// axiom) went 2/2 -> 0/2, both harnesses lost to solver Timeout /
    /// SolverError. With the >=2 rule it is untouched.
    ///
    /// Conservative in the safe direction: a miss just leaves the pre-existing
    /// encoding in place. Calls that only appear after CHC inlining are not
    /// visible here and are not counted.
    fn call_uf_table_needed(&self) -> bool {
        let mut per_symbol: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();
        for block in &self.body.blocks {
            if let Some(key) = self.congruent_call_tag_key(block) {
                *per_symbol.entry(key).or_default() += 1;
            }
        }
        per_symbol.values().any(|sites| *sites >= 2)
    }

    /// The tag key this block's terminator would use, if it is a call either
    /// lane summarises. `None` for anything else.
    fn congruent_call_tag_key(&self, block: &rustc_public::mir::BasicBlock) -> Option<String> {
        let locals = self.body.locals();
        let TerminatorKind::Call { func, args, destination, target: Some(_), .. } =
            &block.terminator.kind
        else {
            return None;
        };
        if args.len() > 8 {
            return None;
        }
        // Lane 2: PURE MATH INTRINSICS. Cheap path first — a call whose
        // arguments are all MIR constants folds exactly in Tier 1 and never
        // needs the table.
        if !args.is_empty() && !args.iter().all(|arg| matches!(arg, Operand::Constant(_))) {
            let path = self.resolve_callee_path(func);
            if let Some(key) = path.as_deref().and_then(math_uf_tag_key) {
                return Some(key);
            }
        }
        // Lane 1: ESTABLISHED-pure scalar callee the precise lane gave up on.
        let dest_ty = destination.ty(locals).ok()?;
        if !ty_is_uf_scalar(dest_ty) {
            return None;
        }
        let instance = resolve_call_instance(func, locals)?;
        let body = instance.body()?;
        let effective = count_effective_blocks(&body);
        let too_big_to_inline = effective
            > super::call::inline_budget::chc_inline_effective_block_limit(&body, effective);
        if !too_big_to_inline && !callee_is_self_recursive(&instance, &body) {
            // The precise inline lane can take it; do not pay a frame column
            // for a call that never reaches the fallback.
            return None;
        }
        established_pure_scalar_callee(&instance).then(|| format!("fn:{}", instance.mangled_name()))
    }
}
