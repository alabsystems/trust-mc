// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Uninterpreted-function summaries for CALLS in the CHC lane, encoded as
//! FIRST-CLASS `declare-fun` symbols (Part of #4270 / TL18; ay 0.23.0 adoption
//! step 8).
//!
//! # The construct
//!
//! A call `d := f(a1..an)` whose callee the encoder cannot translate precisely
//! wants the standard EUF model: `f` is an *arbitrary* symbol (the environment
//! picks it, not the solver), and two applications with equal arguments yield
//! equal results (congruence). SMT-LIB spells that `(declare-fun f (S1..Sn) R)`
//! with `R != Bool`.
//!
//! # The encoding
//!
//! ```text
//! (declare-fun uf_call_<tag>_<callee> (S1 .. Sn) R)   ; never constrained
//! d = (uf_call_<tag>_<callee> a1 .. an)
//! ```
//!
//! One symbol, one signature, per MONOMORPHISED callee (the tag key is the
//! callee's mangled name, so `f::<i32>` and `f::<u32>` are different symbols),
//! and every semantic input of the callee is an argument of the application —
//! the purity gate below only admits callees whose entire input is their
//! by-value scalar parameter list, so "every argument" and "every semantic
//! input" coincide.
//!
//! ## Why this replaced a frozen Array column
//!
//! Until ay 0.23.0, `ay-chc` rejected any `declare-fun` whose return sort was
//! not `Bool`, and the error aborted the parse of the WHOLE problem — one such
//! declaration cost the harness its entire verification. This module therefore
//! emulated the UF as a FROZEN STATE COLUMN, exactly as `float_binop_table.rs`
//! still does for symbolic float arithmetic:
//!
//! ```text
//! call_uf_tbl : Array(BV128 -> BV64)          ; never modified, never constrained
//! d := extract(w-1, 0, select(call_uf_tbl, tag(32) ++ zext(a1 ++ .. ++ an, 96)))
//! ```
//!
//! ay 0.23.0 accepts textual `declare-fun` with scalar `Bool`/`Int`/`Real`/`BV`
//! arguments and a non-`Bool` scalar return as an ordinary uninterpreted
//! function with congruence (`ay-chc/src/parser/commands.rs`: "`declare-rel`
//! and Bool-returning `declare-fun` introduce CHC predicates. Every other
//! `declare-fun` is an ordinary UF retained in `ChcExpr::FuncApp`; the SMT core
//! supplies congruence semantics."). The emulation is therefore obsolete, and
//! it carried three precision ceilings that the real symbol does not:
//!
//!   * a 32-bit callee tag,
//!   * a 96-bit ceiling on the CONCATENATION of all arguments (a two-`u64`
//!     callee was refused outright), and
//!   * a 64-bit ceiling on the value, with narrower returns taking low bits.
//!
//! All three are gone. It also cost an Array-sorted column in EVERY Horn
//! relation of the harness (#4259, the single most expensive thing to add to a
//! relation signature); a `declare-fun` symbol is global and costs no relation
//! width at all.
//!
//! ## Bool-returning callees: BV1, never a Bool `declare-fun`
//!
//! A textual Bool-returning `declare-fun` does NOT mean "uninterpreted
//! predicate" to ay-chc — it means a HORN RELATION (`parse_declare_predicate`
//! routes `return_sort == Bool` to `problem.declare_predicate`). Emitting one
//! for a call summary would hand the solver a relation it is free to SYNTHESISE
//! an interpretation for, which is a different construct entirely and a
//! correctness bug. The CHC lane reaches ay as SMT-LIB TEXT
//! (`emitter::emit_chc_smt2` -> `ChcParser::parse`), so there is no typed
//! back-channel that could say "ordinary UF, Bool return" instead.
//!
//! A `bool`-returning callee is therefore declared with return sort
//! `(_ BitVec 1)` and applied as `d = ((uf ..) == #b1)`. The BV1 symbol is
//! uninterpreted and unconstrained, so `d` ranges over both booleans exactly as
//! a havoc would, and two equal-argument applications are equal — congruence
//! without a Horn relation.
//!
//! ## Symbol/signature stability, and why a mismatch fails closed
//!
//! `ay-chc` type-checks an application against the declaration
//! (`coerce_args_to_sorts`), and a disagreement is a PARSE error that aborts
//! the whole problem. The symbol table is therefore write-once per VC: the
//! first application of a key fixes `(arg_sorts, ret_sort)`, and any later
//! application whose sorts differ is REFUSED — that site keeps its sound havoc
//! rather than risking the harness. Names are `uf_call_<tag>_<sanitised key>`
//! with `tag` a per-VC sequential index, so distinct keys can never produce the
//! same name however the sanitiser folds their characters, and the `uf_call_`
//! prefix cannot collide with a block relation (`<fn>__bb<N>`), the error
//! relations, a state var, or a datatype constructor/selector/tester.
//!
//! # SOUNDNESS — the gate, not the machinery
//!
//! The symbol is never constrained anywhere (not in the entry rule, not in any
//! transition, and no axiom is ever emitted about it), so the real function is
//! one interpretation of it and any property proven over ALL interpretations
//! holds under the real semantics. That much is free. ay's congruence closure
//! is a THEORY fact about the symbol, not evidence that the callee is
//! deterministic — the deterministic-callee claim comes from the gate below and
//! from nowhere else.
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
//! The pre-scan that used to decide whether the Array column was worth its
//! relation width is KEPT verbatim, now as the lane's enable flag. It is no
//! longer paying for a frame column — a `declare-fun` costs no relation width —
//! but it still buys the only thing congruence can buy, and keeping it makes
//! this migration behaviour-preserving on the measured corpus rather than a
//! simultaneous precision AND scheduling change:
//!
//!   * the lane is enabled only when the harness body applies the SAME symbol
//!     at least TWICE (a single application of an unconstrained UF to fixed
//!     arguments is semantically a fresh havoc, so it buys nothing and only
//!     hands the solver a congruence-closure term to carry);
//!   * for the call lane, only for a callee the precise inline lane has already
//!     given up on (too big for `chc_inline_effective_block_limit`, or
//!     self-recursive so the MIR `FunctionInlinePass` skips it);
//!   * math intrinsics with an exact BV encoding (`fabs`, `floor`, `ceil`,
//!     `trunc`, `round`, `copysign`, `minnum`, `maxnum`) are excluded outright:
//!     they are already precise.
//!
//! MEASURED, and the reason the two-site rule exists: with a one-site rule
//! `Intrinsics/Math/Arith/powi.rs` went 2/2 -> 0/2 (both harnesses lost to
//! solver Timeout / SolverError) for a column its single `x.powi(2)` could
//! never use. That particular cost is gone with the column, but the rule is
//! retained deliberately; relaxing it is a separate, separately measured
//! change.

use crate::callee_body::CalleeBody;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    Body, LocalDecl, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;
use trust_mc_core::decl::Decl;

use super::ChcCtx;
use crate::codegen_ay::shared::count_effective_blocks;

/// Prefix of every first-class call-summary UF symbol.
///
/// Must not be a prefix any other symbol generator in this encoder can produce:
/// block relations are `<fn_name>__bb<N>`, error relations `error` /
/// `error_p<N>`, relation padding `__pad_<rel>_<idx>`, state vars `_<local>` /
/// `_<local>__out`, and datatype functions `mk_*` / `fld_*` / `is-*`. A
/// collision would be a hard `ay-chc` parse error ("Cannot declare function
/// 'x': symbol is already declared as a predicate"), which aborts the WHOLE
/// problem, so `ChcCtx::call_uf_symbol` additionally checks the VC's declared
/// relations and variables before committing a name.
const UF_SYMBOL_PREFIX: &str = "uf_call_";

/// How many characters of the (sanitised) tag key are kept in a symbol name.
///
/// Readability only — the sequential tag already makes names injective, so
/// truncation can never merge two callees.
const UF_SYMBOL_KEY_BUDGET: usize = 72;

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

/// One first-class UF symbol, minted once per VC per monomorphised callee.
///
/// `arg_sorts`/`ret_sort` are the DECLARED signature. `ay-chc` type-checks
/// every application against them and a disagreement aborts the parse of the
/// whole problem, so the signature is write-once: a later application whose
/// sorts differ is refused and keeps its sound havoc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct CallUfSymbol {
    /// The SMT symbol name (`uf_call_<tag>_<sanitised key>`).
    pub(in crate::codegen_ay::chc) name: String,
    /// Declared argument sorts.
    pub(in crate::codegen_ay::chc) arg_sorts: Vec<Sort>,
    /// Declared return sort — `BitVec(1)` when the Rust return is `bool`.
    pub(in crate::codegen_ay::chc) ret_sort: Sort,
    /// `true` when the Rust return is `bool` and the declaration says BV1.
    ///
    /// A Bool-returning `declare-fun` is a HORN RELATION to ay-chc, never an
    /// ordinary UF; see the module doc.
    pub(in crate::codegen_ay::chc) bool_result: bool,
}

/// `true` when a sort may appear in a first-class UF signature here.
///
/// `ay-chc` also accepts `Int` and `Real` as scalar UF sorts, but this lane
/// never emits them: the only mode that produces them is int-lift, and the
/// whole lane is skipped there (see `collect_call_uf_congruence_lane`). Keeping
/// the emitted domain to exactly {Bool, BitVec} keeps the declared signature
/// inside the sorts this encoder round-trips through SMT-LIB text every day.
fn sort_is_uf_declarable(sort: &Sort) -> bool {
    sort.is_bool() || sort.is_bitvec()
}

/// Fold a tag key into the SMT-LIB simple-symbol alphabet.
///
/// Lossy on purpose (a mangled name carries `:`, `<`, `>`, `,`, spaces); the
/// sequential tag in front of it is what makes the full name injective, so a
/// fold or a truncation here can never merge two callees onto one symbol.
fn sanitize_uf_key(tag_key: &str) -> String {
    let mut out = String::with_capacity(UF_SYMBOL_KEY_BUDGET);
    for ch in tag_key.chars() {
        if out.len() >= UF_SYMBOL_KEY_BUDGET {
            break;
        }
        out.push(if ch.is_ascii_alphanumeric() { ch } else { '_' });
    }
    out
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
        #[cfg(trust_toolchain)]
        Operand::RuntimeChecks(_) => true,
    }
}

/// `true` when the rvalue reads only frame-local, pointer-free state.
fn rvalue_is_pure(rvalue: &Rvalue, locals: &[LocalDecl]) -> bool {
    match rvalue {
        Rvalue::Use(operand, ..) | Rvalue::Repeat(operand, _) | Rvalue::UnaryOp(_, operand) => {
            operand_is_pure(operand, locals)
        }
        // `sizeof`/`alignof`/`offsetof` — compile-time constants.
        #[cfg(not(trust_toolchain))]
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
        | Rvalue::ThreadLocalRef(_)
        | Rvalue::CopyForDeref(_)
        | Rvalue::Len(_) => false,
        #[cfg(not(trust_toolchain))]
        Rvalue::ShallowInitBox(..) => false,
        // Trust: `Reborrow` re-borrows through a lifetime-carrying ADT (a
        // pointer in disguise), so it is refused like `Ref`.
        #[cfg(trust_toolchain)]
        Rvalue::Reborrow(..) => false,
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
                | StatementKind::PlaceMention(place)
                | StatementKind::AscribeUserType { place, .. } => !place_has_indirection(place),
                #[cfg(not(trust_toolchain))]
                StatementKind::Retag(_, place) => !place_has_indirection(place),
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
    let Some(body) = instance.callee_body() else {
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
    /// Whether the pre-scan enabled the congruence lane for this harness.
    ///
    /// Call sites check this BEFORE translating arguments so that a harness
    /// without the lane takes a byte-identical path to the pre-#4270 encoding
    /// — `translate_operand_with_modified` can register pending declarations,
    /// and a measurement control that perturbs the thing it measures is worse
    /// than no control.
    pub(in crate::codegen_ay::chc) fn call_uf_congruence_enabled(&self) -> bool {
        self.call_uf_congruence
    }

    /// Mint (or look up) the first-class UF symbol for `tag_key`.
    ///
    /// Write-once per key. The first application fixes the declared signature
    /// and emits exactly one `(declare-fun ...)` into the VC; a later
    /// application whose sorts DISAGREE is refused (`None`) so the caller keeps
    /// its sound havoc, because ay-chc type-checks applications against the
    /// declaration and a mismatch aborts the parse of the whole problem.
    ///
    /// Two symbols share a name only if their keys are equal, i.e. only if they
    /// are the SAME monomorphised function: the tag is a per-VC sequential
    /// index over the key map, so the name is injective in the key even though
    /// the sanitiser that renders the key is not.
    fn call_uf_symbol(
        &mut self,
        tag_key: &str,
        arg_sorts: &[Sort],
        ret_sort: &Sort,
        bool_result: bool,
    ) -> Option<CallUfSymbol> {
        if let Some(existing) = self.call_uf_symbols.get(tag_key) {
            // Same callee, incompatible signature at this site: refuse rather
            // than emit an application ay-chc will reject.
            if existing.arg_sorts != arg_sorts
                || existing.ret_sort != *ret_sort
                || existing.bool_result != bool_result
            {
                debug!(
                    tag_key,
                    declared = ?existing,
                    ?arg_sorts,
                    ?ret_sort,
                    "UF summary refused: signature disagrees with the symbol already declared"
                );
                return None;
            }
            return Some(existing.clone());
        }

        let tag = u32::try_from(self.call_uf_symbols.len()).ok()?;
        let name = format!("{UF_SYMBOL_PREFIX}{tag}_{}", sanitize_uf_key(tag_key));
        // Belt-and-braces against the ay-chc "symbol is already declared as a
        // <kind>" parse abort. The `uf_call_` prefix already rules this out by
        // construction; the check costs one scan of two small vectors and turns
        // a whole-harness parse failure into a local fail-closed havoc.
        if self.vc.relations.iter().any(|rel| &*rel.name == name.as_str())
            || self.vc.vars().iter().any(|var| &*var.name == name.as_str())
        {
            debug!(
                tag_key,
                name = name.as_str(),
                "UF summary refused: minted name collides with a declared symbol"
            );
            return None;
        }

        let symbol = CallUfSymbol {
            name: name.clone(),
            arg_sorts: arg_sorts.to_vec(),
            ret_sort: ret_sort.clone(),
            bool_result,
        };
        self.vc.add_decl(Decl::function(name, arg_sorts.to_vec(), ret_sort.clone()));
        self.call_uf_symbols.insert(tag_key.to_string(), symbol.clone());
        Some(symbol)
    }

    /// Build the congruent summary term for `instance(arg_exprs) -> out_sort`.
    ///
    /// `None` — caller keeps its sound havoc — when the lane is disabled, when
    /// any argument or the result is not a UF-declarable scalar, or when the
    /// callee's symbol already carries a different signature.
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
    /// normalise to the SAME symbol, so they are congruent with each other too.
    pub(in crate::codegen_ay::chc) fn math_uf_summary_term(
        &mut self,
        callee_path: &str,
        arg_exprs: &[Expr],
        out_sort: &Sort,
    ) -> Option<Expr> {
        let key = math_uf_tag_key(callee_path)?;
        self.call_uf_summary_term_keyed(&key, arg_exprs, out_sort)
    }

    /// The shared builder: `(uf_call_<tag>_<key> a1 .. an)`, Bool-wrapped when
    /// the Rust return is `bool`.
    ///
    /// Sound whatever it returns: the symbol carries no axiom anywhere in the
    /// problem, so every interpretation of it — including the real function —
    /// is admitted, and `None` simply leaves the caller's havoc alone.
    fn call_uf_summary_term_keyed(
        &mut self,
        tag_key: &str,
        arg_exprs: &[Expr],
        out_sort: &Sort,
    ) -> Option<Expr> {
        if !self.call_uf_congruence {
            return None;
        }
        if !sort_is_uf_declarable(out_sort) {
            return None;
        }
        let arg_sorts: Vec<Sort> = arg_exprs.iter().map(|arg| arg.sort().clone()).collect();
        if !arg_sorts.iter().all(sort_is_uf_declarable) {
            return None;
        }

        // A Bool-returning `declare-fun` is a HORN RELATION to ay-chc, not an
        // ordinary UF (module doc). Declare BV1 and read the bit back instead.
        let bool_result = out_sort.is_bool();
        let ret_sort = if bool_result { Sort::bitvec(1) } else { out_sort.clone() };

        let symbol = self.call_uf_symbol(tag_key, &arg_sorts, &ret_sort, bool_result)?;
        let app = Expr::func_app_with_sort(symbol.name, arg_exprs.to_vec(), symbol.ret_sort);
        Some(if bool_result { app.eq(Expr::bitvec_const(1u128, 1)) } else { app })
    }

    /// Enable the first-class congruent call-summary lane for this body.
    ///
    /// Called from `collect_state_vars` — i.e. before any rule is encoded, so
    /// the flag is stable for the whole encoding. Declares NOTHING by itself:
    /// each callee's `(declare-fun ...)` is minted lazily at its first
    /// application, so a harness whose calls all fail the purity gate emits no
    /// new symbol at all.
    pub(in crate::codegen_ay::chc) fn collect_call_uf_congruence_lane(&mut self) {
        // Measurement control ONLY (same role as
        // `TRUST_MC_NO_STRAIGHTLINE_DISCHARGE`): with the lane disabled, every
        // congruence term degenerates to `None` and both lanes fall back to the
        // exact pre-#4270 encoding. Nothing about soundness depends on it —
        // congruence only ever removes spurious counterexamples. The variable
        // keeps its historical name so existing measurement scripts still work.
        if std::env::var_os("TRUST_MC_NO_CALL_UF_TABLE").is_some() {
            return;
        }
        if !self.call_uf_congruence_pays() {
            return;
        }
        self.call_uf_congruence = true;
        debug!("CHC: enabled first-class congruent call-summary UFs (unconstrained symbols)");
    }

    /// Pre-scan: does this harness contain a call PAIR that congruence can pay
    /// for?
    ///
    /// Congruence buys exactly one thing — two applications of the same symbol
    /// to the same argument value collapse to one term — so it is worth an
    /// uninterpreted symbol ONLY when the body applies the same symbol at least
    /// twice; a lone application of an unconstrained UF to fixed arguments is
    /// semantically a fresh havoc, so it buys no precision and only hands the
    /// solver a congruence-closure term to carry.
    ///
    /// The rule predates the first-class symbols: it was the cost control for
    /// the Array-sorted frame column the lane used to add (#4259). MEASURED
    /// then: with a >=1 rule, `Intrinsics/Math/Arith/powi.rs` (one `x.powi(2)`
    /// per harness, proof `x^2 >= 0` needing only the even-power axiom) went
    /// 2/2 -> 0/2, both harnesses lost to solver Timeout / SolverError. With
    /// the >=2 rule it is untouched. That column is gone, but the rule is
    /// retained so this migration is a pure encoding change; relaxing it is a
    /// separate, separately measured decision.
    ///
    /// Conservative in the safe direction: a miss just leaves the pre-existing
    /// encoding in place. Calls that only appear after CHC inlining are not
    /// visible here and are not counted.
    fn call_uf_congruence_pays(&self) -> bool {
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
        // needs a summary symbol.
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
        let body = instance.callee_body()?;
        let effective = count_effective_blocks(&body);
        let too_big_to_inline = effective
            > super::call::inline_budget::chc_inline_effective_block_limit(&body, effective);
        if !too_big_to_inline && !callee_is_self_recursive(&instance, &body) {
            // The precise inline lane can take it; do not mint a summary
            // symbol for a call that never reaches the fallback.
            return None;
        }
        established_pure_scalar_callee(&instance).then(|| format!("fn:{}", instance.mangled_name()))
    }
}
